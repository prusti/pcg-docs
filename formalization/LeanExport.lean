import PCG.Capability.Order
import MIR
import OpSem
import Core.Export.Lean
import Core.LeanAST

open LeanAST

-- ══════════════════════════════════════════════
-- Definition items
-- ══════════════════════════════════════════════

/-- A tagged definition with its Lean module origin. -/
private inductive LeanDefItem where
  | struct_ (s : StructDef)
  | enum_ (e : EnumDef)
  | fn_ (f : FnDef)
  | property_ (p : PropertyDef)

/-- Infer a namespace for a function from its first
    parameter type, if it matches a known defined type
    in the same module. -/
private def inferNamespace
    (f : FnDef) (definedTypes : List String)
    : Option String :=
  match f.params.head? with
  | some p =>
    match p.ty with
    | .named n =>
      if definedTypes.contains n.name then some n.name
      else none
    | _ => none
  | none => none

private def LeanDefItem.toLeanAST
    (definedTypes : List String)
    : LeanDefItem → LeanDecl
  | .struct_ s => s.toLeanAST
  | .enum_ e => e.toLeanAST
  | .fn_ f =>
    match inferNamespace f definedTypes with
    | some ns => .namespaced ns f.toLeanAST
    | none => f.toLeanAST
  | .property_ p =>
    match inferNamespace p.fnDef definedTypes with
    | some ns => .namespaced ns p.toLeanAST
    | none => p.toLeanAST

/-- All names referenced by this item (types,
    preconditions, called functions). -/
private def LeanDefItem.referencedNames
    : LeanDefItem → List String
  | .struct_ s => s.referencedTypes
  | .enum_ e => e.referencedTypes
  | .fn_ f => f.referencedNames
  | .property_ p => p.fnDef.referencedNames

/-- Whether this item uses `Set` anywhere. -/
private def LeanDefItem.usesSet : LeanDefItem → Bool
  | .struct_ s => s.usesSet
  | .enum_ e => e.usesSet
  | .fn_ f => f.usesSet
  | .property_ p => p.fnDef.usesSet

/-- The type or definition name this item defines. -/
private def LeanDefItem.definedTypeName
    : LeanDefItem → Option String
  | .struct_ s => some s.name
  | .enum_ e => some e.name.name
  | .fn_ f => some f.name
  | .property_ p => some p.fnDef.name

-- ══════════════════════════════════════════════
-- Module grouping and import computation
-- ══════════════════════════════════════════════

/-- Convert a Lean module name to a file path
    (e.g. `MIR.Body` → `MIR/Body.lean`). -/
private def moduleToPath (mod : Lean.Name) : String :=
  let components := mod.components.map toString
  "/".intercalate components ++ ".lean"

/-- Topologically sort definition items so that types
    are defined before they are referenced. -/
private def topoSort
    (items : List LeanDefItem) : List LeanDefItem :=
  let getName (i : LeanDefItem) : Option String :=
    i.definedTypeName
  let getRefs (i : LeanDefItem) : List String :=
    i.referencedNames
  let defined := items.filterMap getName
  let rec go
      (remaining : List LeanDefItem)
      (emitted : List String)
      (acc : List LeanDefItem)
      (fuel : Nat)
      : List LeanDefItem :=
    match fuel with
    | 0 => acc ++ remaining
    | fuel + 1 =>
      if remaining.isEmpty then acc
      else
        let (ready, blocked) := remaining.partition
          fun item =>
            let refs := getRefs item
            refs.all fun r =>
              emitted.contains r || !defined.contains r
        if ready.isEmpty then acc ++ remaining
        else
          let newEmitted := emitted ++
            ready.filterMap getName
          go blocked newEmitted (acc ++ ready) fuel
  go items [] [] (items.length + 1)

/-- Group definitions by Lean module, preserving
    registration order within each module. -/
private def buildModules
    (enums : List RegisteredEnum)
    (structs : List RegisteredStruct)
    (fns : List RegisteredFn)
    (properties : List RegisteredProperty)
    : List (Lean.Name × List LeanDefItem) :=
  let tagged : List (Lean.Name × LeanDefItem) :=
    (structs.map fun s =>
      (s.leanModule, .struct_ s.structDef)) ++
    (enums.map fun e =>
      (e.leanModule, .enum_ e.enumDef)) ++
    (properties.map fun p =>
      (p.leanModule, .property_ p.propertyDef)) ++
    (fns.map fun f =>
      (f.leanModule, .fn_ f.fnDef))
  let allModNames := tagged.map (·.1)
  let uniqueMods := allModNames.foldl (init := [])
    fun acc m => if acc.contains m then acc
      else acc ++ [m]
  uniqueMods.map fun mod =>
    let items := tagged.filter (·.1 == mod)
      |>.map (·.2)
    (mod, topoSort items)

/-- Build a map from type name to the module that
    defines it. -/
private def typeToModuleMap
    (modules : List (Lean.Name × List LeanDefItem))
    : List (String × Lean.Name) :=
  modules.flatMap fun (mod, items) =>
    items.filterMap fun item =>
      item.definedTypeName.map (·, mod)

/-- Compute the imports for a module based on its
    type references. -/
private def computeImports
    (mod : Lean.Name)
    (items : List LeanDefItem)
    (typeMap : List (String × Lean.Name))
    : List Lean.Name :=
  let refdTypes := items.flatMap
    LeanDefItem.referencedNames
  let needsSet := items.any LeanDefItem.usesSet
  let depMods := refdTypes.filterMap fun tn =>
    typeMap.find? (·.1 == tn) |>.map (·.2)
  let depMods := depMods.filter (· != mod)
  let unique := depMods.foldl (init := [])
    fun acc m => if acc.contains m then acc
      else acc ++ [m]
  let setImport :=
    if needsSet then [`Util.Set] else []
  setImport ++ unique

/-- Build the `LeanModule` AST for a module. -/
private def buildLeanModule
    (items : List LeanDefItem)
    (imports : List Lean.Name)
    : LeanModule :=
  let definedTypes := items.filterMap
    LeanDefItem.definedTypeName
  { imports := imports.map toString
    decls := items.map
      (LeanDefItem.toLeanAST definedTypes) }

/-- Render a module to Lean source. -/
private def renderModule
    (items : List LeanDefItem)
    (imports : List Lean.Name)
    : String :=
  toString (buildLeanModule items imports)

-- ══════════════════════════════════════════════
-- Project scaffolding
-- ══════════════════════════════════════════════

private def leanToolchain : String :=
  "leanprover/lean4:v4.30.0-rc1\n"

private def genLakefile
    (libs : List String) : String :=
  let libDecls := libs.map fun l =>
    s!"@[default_target]\nlean_lib {l} where\n\
       srcDir := \".\""
  s!"import Lake\n\
     open Lake DSL\n\
     \n\
     package formalization where\n\
       leanOptions := #[\n\
         ⟨`autoImplicit, false⟩\n\
       ]\n\
     \n\
     require batteries from\n\
       git \
     \"https://github.com/leanprover-community/batteries\"\n\
         @ \"main\"\n\
     \n\
     {"\n\n".intercalate libDecls}\n"

private def setModule : String :=
  "import Std.Data.HashSet\n\
   \n\
   abbrev Set (α : Type) [BEq α] [Hashable α] :=\n\
     Std.HashSet α\n\
   \n\
   namespace Set\n\
   \n\
   def singleton {α : Type} [BEq α] [Hashable α]\n\
       (a : α) : Set α :=\n\
     (∅ : Std.HashSet α).insert a\n\
   \n\
   def union {α : Type} [BEq α] [Hashable α]\n\
       (s₁ s₂ : Set α) : Set α :=\n\
     Std.HashSet.union s₁ s₂\n\
   \n\
   instance (α : Type) [BEq α] [Hashable α]\n\
       : Append (Set α) := ⟨union⟩\n\
   \n\
   def ofOption {α : Type} [BEq α] [Hashable α]\n\
       : Option α → Set α\n\
     | some a => singleton a\n\
     | none => ∅\n\
   \n\
   def flatMapList {α : Type} {β : Type}\n\
       [BEq β] [Hashable β]\n\
       (l : List α) (f : α → Set β) : Set β :=\n\
     l.foldl (fun (acc : Std.HashSet β) x =>\n\
       Std.HashSet.union acc (f x)) ∅\n\
   \n\
   end Set\n\
   \n\
   namespace Option\n\
   \n\
   def toSet {α : Type} [BEq α] [Hashable α]\n\
       (o : Option α) : Set α :=\n\
     Set.ofOption o\n\
   \n\
   end Option\n"

-- ══════════════════════════════════════════════
-- File I/O
-- ══════════════════════════════════════════════

private def writeFile
    (path : String) (contents : String) : IO Unit := do
  let dir := System.FilePath.mk path |>.parent
    |>.getD (System.FilePath.mk ".")
  IO.FS.createDirAll dir
  IO.FS.writeFile ⟨path⟩ contents
  IO.println s!"  wrote {path}"

-- ══════════════════════════════════════════════
-- Main
-- ══════════════════════════════════════════════

def main (args : List String) : IO Unit := do
  let outDir := args.head? |>.getD "generated/lean"
  let enums ← getRegisteredEnums
  let structs ← getRegisteredStructs
  let fns ← getRegisteredFns
  let props ← getRegisteredProperties
  let modules := buildModules enums structs fns props
  let typeMap := typeToModuleMap modules
  -- Collect top-level lib names (e.g. MIR, PCG, OpSem)
  let topLibs := modules.map
    fun (m, _) => m.getRoot.toString
  let uniqueLibs := topLibs.foldl (init := [])
    fun acc l => if acc.contains l then acc
      else acc ++ [l]
  let libs := ["Util"] ++ uniqueLibs
  -- Write project scaffolding
  writeFile s!"{outDir}/lean-toolchain" leanToolchain
  writeFile s!"{outDir}/lakefile.lean" (genLakefile libs)
  writeFile s!"{outDir}/Util/Set.lean" setModule
  -- Write module files
  for (mod, items) in modules do
    let imports := computeImports mod items typeMap
    let path := s!"{outDir}/{moduleToPath mod}"
    let contents := renderModule items imports
    writeFile path contents
  -- Write root files for each lean_lib
  for lib in uniqueLibs do
    let libMods := modules.filter
      fun (m, _) => m.getRoot.toString == lib
    let importLines := libMods.map
      fun (m, _) => s!"import {m}"
    let rootContents :=
      "\n".intercalate importLines ++ "\n"
    writeFile s!"{outDir}/{lib}.lean" rootContents
  -- Write root file for Util
  writeFile s!"{outDir}/Util.lean" "import Util.Set\n"
  -- Build the generated project
  IO.println "  building generated project..."
  let buildResult ← IO.Process.output {
    cmd := "lake"
    args := #["build"]
    cwd := some outDir
  }
  if buildResult.exitCode == 0 then
    IO.println "  built successfully"
  else
    IO.eprintln s!"  lake build failed:\n\
      {buildResult.stderr}"
    IO.Process.exit 1
