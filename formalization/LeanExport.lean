import PCG.AbstractionEdge
import PCG.Capability.Order
import PCG.LifetimeProjection
import PCG.LifetimeProjectionLabel
import PCG.LocalLifetimeProjection
import PCG.MaybeLabelledPlace
import PCG.PcgNode
import PCG.PcgPlace
import PCG.UnpackEdge
import MIR
import OpSem
import Core.Export.Lean
import Core.LeanAST

open LeanAST

/-- Position of extra Lean code relative to auto-generated
    definitions. `middle` inserts between type definitions
    (structs/enums) and function definitions. -/
private inductive ExtraPos where
  | before | middle | after
  deriving BEq

/-- Extra raw Lean code for specific generated modules.
    Each entry is `(moduleName, position, rawLeanCode)`.

    Entries here should be added only in exceptional cases:
    anything that can be expressed as a `defFn` (or
    `defStruct`/`defEnum`/`defProperty`) belongs in the DSL
    source so that it participates in Rust/LaTeX export as
    well. Reserve this list for constructs the DSL cannot
    represent — typeclass instances, Lean-only helpers that
    use features outside the DSL grammar, etc. -/
private def extraLeanItems :
    List (Lean.Name × ExtraPos × String) :=
  [ (`OpSem.Decode, .before,
"/-- Encode a natural number as `numBytes` little-endian
    abstract bytes (least-significant byte first). -/
def encodeLeUnsigned (n : Nat) : Nat → List AbstractByte
  | 0 => []
  | k + 1 =>
    .init (UInt8.ofNat (n % 256)) ::
      encodeLeUnsigned (n / 256) k

/-- Build an `IntValue` from a decoded natural number
    based on the target size (in bytes). -/
def intValueOfNat : Nat → Nat → Option IntValue
  | 1, n => some (.u8 (UInt8.ofNat n))
  | 2, n => some (.u16 (UInt16.ofNat n))
  | 4, n => some (.u32 (UInt32.ofNat n))
  | 8, n => some (.u64 (UInt64.ofNat n))
  | _, _ => none
")
  , (`OpSem.Address, .after,
"instance : LT Address where
  lt a b := a.addr < b.addr

instance : LE Address where
  le a b := a.addr ≤ b.addr

instance (a b : Address) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.addr < b.addr))

instance (a b : Address) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.addr ≤ b.addr))

instance : DecidableEq Address :=
  fun a b => if h : a.addr = b.addr
    then isTrue (by cases a; cases b; simp_all)
    else isFalse (by intro heq; cases heq; exact h rfl)

instance : HSub Address Address Nat where
  hSub a b := a.addr - b.addr

instance : HAdd Address Nat Address where
  hAdd a n := ⟨a.addr + n⟩
")
  , (`OpSem.Memory, .before,
"def last := @List.getLast?
def replicate := @List.replicate
def listSet := @List.set
def listTake := @List.take
def listDrop := @List.drop

open AbstractByte
")
  ]

-- ══════════════════════════════════════════════
-- Definition items
-- ══════════════════════════════════════════════

/-- A tagged definition with its Lean module origin. -/
private inductive LeanDefItem where
  | struct_ (s : StructDef)
  | enum_ (e : EnumDef)
  | alias_ (a : AliasDef)
  | fn_ (f : FnDef)
  | property_ (p : PropertyDef)

/-- Infer a namespace for a function from its first
    parameter type, if it matches a known type. -/
private def inferNamespace
    (f : FnDef) (allTypes : List String)
    : Option String :=
  match f.params.head? with
  | some p =>
    match p.ty with
    | .named n =>
      if allTypes.contains n.name then some n.name
      else none
    | _ => none
  | none => none

private def LeanDefItem.toLeanAST
    (definedTypes : List String)
    : LeanDefItem → LeanDecl
  | .struct_ s => s.toLeanAST
  | .enum_ e => e.toLeanAST
  | .alias_ a => a.toLeanAST
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
  | .alias_ a => a.referencedTypes
  | .fn_ f => f.referencedNames
  | .property_ p => p.fnDef.referencedNames

/-- Whether this item uses `Set` anywhere. -/
private def LeanDefItem.usesSet : LeanDefItem → Bool
  | .struct_ s => s.usesSet
  | .enum_ e => e.usesSet
  | .alias_ a => a.usesSet
  | .fn_ f => f.usesSet
  | .property_ p => p.fnDef.usesSet

/-- Whether this item is a type definition (struct/enum/alias)
    as opposed to a function/property. -/
private def LeanDefItem.isTypeDef : LeanDefItem → Bool
  | .struct_ _ => true
  | .enum_ _ => true
  | .alias_ _ => true
  | .fn_ _ => false
  | .property_ _ => false

/-- Get the FnDef for function/property items. -/
private def LeanDefItem.fnDef? : LeanDefItem → Option FnDef
  | .fn_ f => some f
  | .property_ p => some p.fnDef
  | _ => none

/-- The type or definition name this item defines. -/
private def LeanDefItem.definedTypeName
    : LeanDefItem → Option String
  | .struct_ s => some s.name
  | .enum_ e => some e.name.name
  | .alias_ a => some a.name
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
    are defined before they are referenced. Self-references
    (recursive types) are treated as already satisfied. -/
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
            let selfName := getName item
            let refs := getRefs item
            refs.all fun r =>
              selfName == some r ||
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
    (aliases : List RegisteredAlias)
    (fns : List RegisteredFn)
    (properties : List RegisteredProperty)
    : List (Lean.Name × List LeanDefItem) :=
  let tagged : List (Lean.Name × LeanDefItem) :=
    (structs.map fun s =>
      (s.leanModule, .struct_ s.structDef)) ++
    (enums.map fun e =>
      (e.leanModule, .enum_ e.enumDef)) ++
    (aliases.map fun a =>
      (a.leanModule, .alias_ a.aliasDef)) ++
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
  let mapHelpers := ["mapGet", "mapEmpty", "mapSingleton",
                      "mapUnionSets"]
  let needsMap := mapHelpers.any refdTypes.contains
  let depMods := refdTypes.filterMap fun tn =>
    typeMap.find? (·.1 == tn) |>.map (·.2)
  let depMods := depMods.filter (· != mod)
  let unique := depMods.foldl (init := [])
    fun acc m => if acc.contains m then acc
      else acc ++ [m]
  let runtimeImports :=
    (if needsSet then [`Runtime.Set] else []) ++
    (if needsMap then [`Runtime.Map] else [])
  runtimeImports ++ unique

/-- Build a map from function name to its inferred
    namespace, across all modules. -/
private def fnNamespaceMap
    (modules : List (Lean.Name × List LeanDefItem))
    (allTypes : List String)
    : List (String × String) :=
  modules.flatMap fun (_, items) =>
    items.filterMap fun item =>
      item.fnDef?.bind fun f =>
        (inferNamespace f allTypes).map (f.name, ·)

/-- Compute which namespaces need to be opened in a
    module so that cross-namespace calls resolve. -/
private def computeOpens
    (items : List LeanDefItem)
    (nsMap : List (String × String))
    : List String :=
  let calledFns := items.flatMap fun item =>
    match item with
    | .fn_ f => f.body.calledNames
    | .property_ p => p.fnDef.body.calledNames
    | _ => []
  let needed := calledFns.filterMap fun fn =>
    nsMap.find? (·.1 == fn) |>.map (·.2)
  needed.foldl (init := []) fun acc ns =>
    if acc.contains ns then acc else acc ++ [ns]

/-- Render a module to Lean source, with optional
    extra code before/between/after auto-generated defs.
    `middle` extras are inserted between type definitions
    (structs/enums) and function/property definitions. -/
private def renderModule
    (items : List LeanDefItem)
    (imports : List Lean.Name)
    (allTypes : List String)
    (opens : List String := [])
    (extrasBefore : List String := [])
    (extrasMiddle : List String := [])
    (extrasAfter : List String := [])
    : String :=
  let toLeanAST := LeanDefItem.toLeanAST allTypes
  let importStr := imports.map toString |>.map
    (s!"import {·}") |> "\n".intercalate
  let openStr := if opens.isEmpty then ""
    else "\nopen " ++ " ".intercalate opens ++ "\n"
  let beforeStr := if extrasBefore.isEmpty then ""
    else "\n" ++ "\n".intercalate extrasBefore ++ "\n"
  let afterStr := if extrasAfter.isEmpty then ""
    else "\n\n" ++ "\n".intercalate extrasAfter
  -- Split items into types (structs/enums) and code
  -- (fns/properties) so opens and middle extras can be
  -- placed after types but before code.
  let (typeDefs, codeDefs) :=
    items.partition LeanDefItem.isTypeDef
  let typeStr := typeDefs.map (toString ∘ toLeanAST)
    |> "\n\n".intercalate
  let middleStr := if extrasMiddle.isEmpty then ""
    else "\n" ++ "\n".intercalate extrasMiddle ++ "\n"
  let codeStr := codeDefs.map (toString ∘ toLeanAST)
    |> "\n\n".intercalate
  let codeBlock := if codeDefs.isEmpty then ""
    else s!"\n{codeStr}\n"
  s!"{importStr}\n{beforeStr}\n{typeStr}\n\
     {openStr}{middleStr}{codeBlock}{afterStr}\n"

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
     {"\n\n".intercalate libDecls}\n"

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
  let aliases ← getRegisteredAliases
  let fns ← getRegisteredFns
  let props ← getRegisteredProperties
  let modules :=
    buildModules enums structs aliases fns props
  let typeMap := typeToModuleMap modules
  let allTypes := typeMap.map (·.1)
  let nsMap := fnNamespaceMap modules allTypes
  -- Collect top-level lib names (e.g. MIR, PCG, OpSem)
  let topLibs := modules.map
    fun (m, _) => m.getRoot.toString
  let uniqueLibs := topLibs.foldl (init := [])
    fun acc l => if acc.contains l then acc
      else acc ++ [l]
  let libs := ["Runtime"] ++ uniqueLibs
  -- Write project scaffolding
  writeFile s!"{outDir}/lean-toolchain" leanToolchain
  writeFile s!"{outDir}/lakefile.lean" (genLakefile libs)
  -- Copy the entire `Runtime/` folder (source-of-truth for
  -- `Set`, `Map`, `mapGet`, and related helpers) into the
  -- generated project.
  let runtimeDir : System.FilePath := "Runtime"
  let outRuntime : System.FilePath := s!"{outDir}/Runtime"
  IO.FS.createDirAll outRuntime
  for entry in ← runtimeDir.readDir do
    if entry.path.extension == some "lean" then
      let contents ← IO.FS.readFile entry.path
      writeFile s!"{outDir}/Runtime/{entry.fileName}"
        contents
  -- Write module files
  for (mod, items) in modules do
    let imports := computeImports mod items typeMap
    let extrasFor (pos : ExtraPos) :=
      extraLeanItems.filterMap fun (m, p, code) =>
        if m == mod && p == pos then some code else none
    let opens := computeOpens items nsMap
    let path := s!"{outDir}/{moduleToPath mod}"
    let contents := renderModule items imports allTypes
      opens (extrasFor .before) (extrasFor .middle)
      (extrasFor .after)
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
  -- Write root file for Runtime
  writeFile s!"{outDir}/Runtime.lean"
    "import Runtime.Set\nimport Runtime.Map\n"
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
