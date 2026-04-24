import PCG.BorrowsGraph
import PCG.Capability.Order
import PCG.Edges
import PCG.Nodes
import PCG.Obtain
import PCG.PcgData
import PCG.PlaceCapability
import PCG.PlaceTriple
import PCG.TransientState
import PCG.ValidityConditions
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
  , (`PCG.Owned.InitTree, .middle,
"def placeIsOwnedIn (body : Body) (p : Place) : Prop :=
  ∃ h : validPlace body p, isOwned body p h = true
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
  | inductiveProperty_ (p : InductivePropertyDef)

/-- Infer a namespace for a function from its first
    parameter type, if it matches a known non-alias type.
    Alias type names are excluded because `namespace <alias>`
    does not create a valid namespace the generated code can
    `open` from the top of the file. -/
private def inferNamespace
    (f : FnDef) (allTypes : List String)
    (aliasNames : List String := [])
    : Option String :=
  let headName : DSLType → Option String
    | .named n => some n.name
    | .app head _ => some head.name
    | _ => none
  match f.params.head? with
  | some p =>
    match headName p.ty with
    | some n =>
      if aliasNames.contains n then none
      else if allTypes.contains n then some n
      else none
    | none => none
  | none => none

private def LeanDefItem.toLeanAST
    (definedTypes : List String)
    (aliasNames : List String)
    (mapSetTypes : List String)
    : LeanDefItem → LeanDecl
  | .struct_ s => s.toLeanASTWith mapSetTypes
  | .enum_ e => e.toLeanAST
  | .alias_ a => a.toLeanAST
  | .fn_ f =>
    -- Functions belonging to a mutual-recursion group are
    -- emitted together inside a single `mutual … end` block
    -- at render time, so they can't sit inside a per-function
    -- `namespace`.
    if f.mutualGroup.isSome then f.toLeanAST
    else
      match inferNamespace f definedTypes aliasNames with
      | some ns => .namespaced ns f.toLeanAST
      | none => f.toLeanAST
  | .property_ p =>
    match inferNamespace p.fnDef definedTypes aliasNames with
    | some ns => .namespaced ns p.toLeanAST
    | none => p.toLeanAST
  | .inductiveProperty_ p => p.toLeanAST

/-- All names referenced by this item (types,
    preconditions, called functions). -/
private def LeanDefItem.referencedNames
    : LeanDefItem → List String
  | .struct_ s => s.referencedTypes
  | .enum_ e => e.referencedTypes
  | .alias_ a => a.referencedTypes
  | .fn_ f => f.referencedNames
  | .property_ p => p.fnDef.referencedNames
  | .inductiveProperty_ p => p.referencedTypes

/-- Whether this item uses `Set` anywhere. -/
private def LeanDefItem.usesSet : LeanDefItem → Bool
  | .struct_ s => s.usesSet
  | .enum_ e => e.usesSet
  | .alias_ a => a.usesSet
  | .fn_ f => f.usesSet
  | .property_ p => p.fnDef.usesSet
  | .inductiveProperty_ p => p.usesSet

/-- Whether this item is a type definition (struct/enum/alias)
    as opposed to a function/property. -/
private def LeanDefItem.isTypeDef : LeanDefItem → Bool
  | .struct_ _ => true
  | .enum_ _ => true
  | .alias_ _ => true
  | .fn_ _ => false
  | .property_ _ => false
  | .inductiveProperty_ _ => true

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
  | .inductiveProperty_ p => some p.name

-- ══════════════════════════════════════════════
-- Module grouping and import computation
-- ══════════════════════════════════════════════

/-- Convert a Lean module name to a file path
    (e.g. `MIR.Body` → `MIR/Body.lean`). -/
private def moduleToPath (mod : Lean.Name) : String :=
  let components := mod.components.map toString
  "/".intercalate components ++ ".lean"

/-- The mutual-group tag of an item, if any. Used by
    `topoSort` so members of a mutual group are considered
    satisfied by each other, and by `groupByMutual` below
    to emit adjacent group members together. -/
private def LeanDefItem.mutualGroupTag
    : LeanDefItem → Option String
  | .fn_ f => f.mutualGroup
  | _ => none

/-- Topologically sort definition items so that types
    are defined before they are referenced. Self-references
    (recursive types) are treated as already satisfied, as
    are references to other members of the same mutual
    group so that an entire mutual block can be emitted at
    once. -/
private def topoSort
    (items : List LeanDefItem) : List LeanDefItem :=
  let getName (i : LeanDefItem) : Option String :=
    i.definedTypeName
  -- A reference may be qualified (`BorrowsGraph.placeIsBlocked`
  -- when called cross-namespace); strip the prefix so it matches
  -- the short names stored in `definedTypeName`.
  let shortName (n : String) : String :=
    (n.splitOn ".").getLast?.getD n
  let getRefs (i : LeanDefItem) : List String :=
    i.referencedNames.map shortName
  let defined := items.filterMap getName
  -- For each mutual group tag, the names of every item in
  -- that group. Members of the same group can be emitted
  -- together without any having been emitted first.
  let groupMembers : List (String × List String) :=
    items.foldl (init := []) fun acc i =>
      match i.mutualGroupTag, getName i with
      | some tag, some n =>
        match acc.find? (·.1 == tag) with
        | some (_, ns) =>
          (acc.filter (·.1 != tag)) ++ [(tag, ns ++ [n])]
        | none => acc ++ [(tag, [n])]
      | _, _ => acc
  let isReady (item : LeanDefItem) (emitted : List String)
      : Bool :=
    let selfName := getName item
    let ownGroup : List String :=
      match item.mutualGroupTag with
      | some tag =>
        (groupMembers.find? (·.1 == tag)).map
          (·.2) |>.getD []
      | none => []
    let refs := getRefs item
    refs.all fun r =>
      selfName == some r ||
      emitted.contains r || !defined.contains r ||
      ownGroup.contains r
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
        -- A mutual-group item only becomes ready when every
        -- member of its group is ready, so the entire group
        -- can be emitted contiguously and `groupByMutual`
        -- can wrap them in a single `mutual … end` block.
        let groupReady (tag : String) : Bool :=
          remaining.all fun other =>
            other.mutualGroupTag != some tag ||
              isReady other emitted
        let (ready, blocked) := remaining.partition
          fun item =>
            isReady item emitted &&
              (match item.mutualGroupTag with
               | some tag => groupReady tag
               | none => true)
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
    (inductiveProps : List RegisteredInductiveProperty)
    : List (Lean.Name × List LeanDefItem) :=
  let tagged : List (Lean.Name × LeanDefItem) :=
    (structs.map fun s =>
      (s.leanModule, .struct_ s.structDef)) ++
    (enums.map fun e =>
      (e.leanModule, .enum_ e.enumDef)) ++
    (aliases.map fun a =>
      (a.leanModule, .alias_ a.aliasDef)) ++
    (inductiveProps.map fun p =>
      (p.leanModule,
       .inductiveProperty_ p.inductivePropertyDef)) ++
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
    type and function references. -/
private def computeImports
    (mod : Lean.Name)
    (items : List LeanDefItem)
    (typeMap : List (String × Lean.Name))
    (fnMap : List (String × Lean.Name) := [])
    : List Lean.Name :=
  let refdTypes := items.flatMap
    LeanDefItem.referencedNames
  let needsSet := items.any LeanDefItem.usesSet
  let mapHelpers := ["mapGet", "mapEmpty", "mapSingleton",
                      "mapUnionSets", "mapInsert", "mapRemove"]
  let needsMap := mapHelpers.any refdTypes.contains
  -- Lookup both by short name and by the last segment of a
  -- qualified reference, so `Ty.layout` resolves via the `layout`
  -- entry fnMap registers.
  let shortName (n : String) : String :=
    (n.splitOn ".").getLast?.getD n
  let typeDeps := refdTypes.filterMap fun tn =>
    typeMap.find? (·.1 == tn) |>.map (·.2)
  let fnDeps := refdTypes.filterMap fun fn =>
    fnMap.find? (·.1 == shortName fn) |>.map (·.2)
  let depMods := (typeDeps ++ fnDeps).filter (· != mod)
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
    (aliasNames : List String)
    : List (String × String) :=
  modules.flatMap fun (_, items) =>
    items.filterMap fun item =>
      item.fnDef?.bind fun f =>
        (inferNamespace f allTypes aliasNames).map (f.name, ·)

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

/-- Group consecutive items by mutual-group tag: adjacent
    items sharing a non-`none` tag become one sub-list. -/
private def groupByMutual
    (items : List LeanDefItem)
    : List (List LeanDefItem) :=
  items.foldl (init := []) fun acc item =>
    match acc.getLast?, item.mutualGroupTag with
    | some last, some tag =>
      match last.head?.bind LeanDefItem.mutualGroupTag with
      | some lastTag =>
        if lastTag == tag then
          acc.dropLast ++ [last ++ [item]]
        else acc ++ [[item]]
      | none => acc ++ [[item]]
    | _, _ => acc ++ [[item]]

/-- Compute the names of structs whose fields hold (directly
    or transitively through another struct) a `Map`/`Set`. The
    generated Lean project needs this because `HashMap`/`HashSet`
    do not derive `BEq`/`Hashable`, so any wrapping struct must
    omit those derives as well. Iterated to a fixed point. -/
private def computeMapSetTypes
    (structs : List RegisteredStruct) : List String :=
  let directUsers : List String := structs.filterMap fun rs =>
    let anyDirect := rs.structDef.fields.any fun f =>
      f.ty.usesMap || f.ty.usesSet
    if anyDirect then some rs.structDef.name else none
  let rec loop (known : List String)
      (fuel : Nat) : List String :=
    match fuel with
    | 0 => known
    | fuel + 1 =>
      let newly : List String := structs.filterMap fun rs =>
        if known.contains rs.structDef.name then none
        else if rs.structDef.fields.any fun f =>
            f.ty.namedTypes.any fun n => known.contains n
        then some rs.structDef.name
        else none
      if newly.isEmpty then known
      else loop (known ++ newly) fuel
  loop directUsers structs.length

/-- Render a module to Lean source, with optional
    extra code before/between/after auto-generated defs.
    `middle` extras are inserted between type definitions
    (structs/enums) and function/property definitions. -/
private def renderModule
    (items : List LeanDefItem)
    (imports : List Lean.Name)
    (allTypes : List String)
    (aliasNames : List String)
    (mapSetTypes : List String)
    (opens : List String := [])
    (extrasBefore : List String := [])
    (extrasMiddle : List String := [])
    (extrasAfter : List String := [])
    : String :=
  let toLeanAST :=
    LeanDefItem.toLeanAST allTypes aliasNames mapSetTypes
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
  let renderGroup (group : List LeanDefItem) : String :=
    let hasMutualTag := group.any fun i =>
      i.mutualGroupTag.isSome
    let rendered := group.map (toString ∘ toLeanAST)
    if hasMutualTag && group.length > 1 then
      "mutual\n" ++ "\n".intercalate rendered ++ "\nend"
    else
      "\n\n".intercalate rendered
  let codeStr := (groupByMutual codeDefs).map renderGroup
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
  let inductiveProps ← getRegisteredInductiveProperties
  let modules :=
    buildModules enums structs aliases fns props
      inductiveProps
  let typeMap := typeToModuleMap modules
  let allTypes := typeMap.map (·.1)
  let aliasNames := aliases.map (·.aliasDef.name)
  let nsMap := fnNamespaceMap modules allTypes aliasNames
  let mapSetTypes := computeMapSetTypes structs
  -- Map every registered function name to the module it lives
  -- in so `computeImports` can pull in cross-module callees.
  let fnMap : List (String × Lean.Name) :=
    modules.flatMap fun (mod, items) =>
      items.filterMap fun item =>
        item.fnDef?.map fun f => (f.name, mod)
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
    let imports := computeImports mod items typeMap fnMap
    let extrasFor (pos : ExtraPos) :=
      extraLeanItems.filterMap fun (m, p, code) =>
        if m == mod && p == pos then some code else none
    let opens := computeOpens items nsMap
    let path := s!"{outDir}/{moduleToPath mod}"
    let contents := renderModule items imports allTypes
      aliasNames mapSetTypes opens (extrasFor .before)
      (extrasFor .middle) (extrasFor .after)
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
