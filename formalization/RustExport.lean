import PCG.AnalysisObject
import PCG.BorrowsGraph
import PCG.Capability.Order
import PCG.DomainData
import PCG.Edges
import PCG.EvalStmtData
import PCG.Nodes
import PCG.Analyze.PlaceTriple
import PCG.TransientState
import PCG.ValidityConditions
import MIR
import OpSem
import Core.Export.Rust
import Core.Dsl.Types.OrderDef

-- The `PCG.Obtain` submodule (`PCG.Obtain.Tree`,
-- `PCG.Obtain.Owned`, `PCG.Obtain.PcgData`) is deliberately
-- not imported here: its `defFn` bodies use constructs the
-- Rust exporter does not yet lower faithfully (bare-dotted
-- variants whose enum must be disambiguated from the
-- surrounding type, function-level pattern destructuring of
-- `⟨a, b, c⟩` tuples, etc.), and importing it shifts the
-- enum registration order enough to mis-resolve unqualified
-- `.deref` in previously-working modules
-- (`InitTree.itPlaces`, `InitialisationState.meet`).
-- The Lean and LaTeX exports remain the authoritative source
-- for `obtain` until the Rust exporter can translate these
-- forms on its own; see `rustUnsupported` below for the
-- companion blocklist used should the import ever return.
--
-- `PCG.Analyze.AnalysisObject` is similarly not imported:
-- its triple-construction helpers reference `Capability.X`
-- as a fully-qualified ident (which the Rust exporter
-- mis-renders as the lowercased module path
-- `capability.X`) and need cross-crate `use` directives
-- for `Operand`, `Statement`, `Rvalue`, `Mutability`,
-- `Place`, and `Terminator` that the exporter does not
-- inject automatically.
--
-- `PCG.PcgData` (and the alias `PCG.PcgDomainData` that
-- references it) are likewise not imported: `PcgData` pulls
-- in `PCG.Owned.InitTree` / `PCG.Owned.OwnedState`, whose
-- `defFn` bodies use bare-dotted variants (`.uninit`,
-- `.unallocated`, `.deep`, …) that the Rust exporter cannot
-- yet disambiguate against the surrounding type. Lean and
-- LaTeX remain the authoritative exports for these types
-- until the exporter handles the construct.

/-- Extra Rust content for a single generated module that
    cannot be auto-generated from `defEnum` / `defStruct`
    (e.g. trait impls, helper functions, hand-rolled `use`
    directives). Items go to the module body; uses go to the
    module's `extraUses` list and render as `use ...;` lines.
    Splitting these channels means an entry cannot accidentally
    place a `use` directive in `items` (where it would render
    after the auto-generated imports) or a structured item in
    `uses` (which would mangle it). -/
structure ExtraSpec where
  /-- Lean-side crate prefix (e.g. `"PCG"`, `"OpSem"`). Used
      by `buildCrate` to filter specs to the current crate. -/
  cratePrefix : String
  /-- Snake-case Rust module name (e.g. `"borrowchecker"`). -/
  rustModule  : String
  /-- `use` directive bodies (no `use ` prefix, no trailing
      `;`). Rendered alongside the auto-generated imports. -/
  uses        : List String := []
  /-- Top-level Rust items (impls, fns, raw blocks). -/
  items       : List RustItem := []

/-- Extra Rust content keyed by `(cratePrefix, rustModule)`.
    Each entry contributes `use` directives (rendered through
    `RustModule.extraUses`) and/or items (rendered into the
    module body). -/
def extras : List ExtraSpec :=
  [ { cratePrefix := "PCG", rustModule := "borrowchecker"
    , uses := [ "formal_mir::body::Location"
              , "crate::pcgnode::PcgNode" ] }
  , { cratePrefix := "PCG", rustModule := "analysislocation"
    , uses := [ "formal_mir::body::Location" ] }
  , { cratePrefix := "PCG", rustModule := "analysisobject"
    , uses :=
        [ "formal_mir::body::{Body, Terminator, \
           valid_statement, valid_terminator}"
        , "formal_mir::statements::Statement" ] }
  , { cratePrefix := "PCG", rustModule := "borrowedge"
    , uses := [ "formal_mir::body::Location"
              , "formal_mir::region::Region"
              , "formal_mir::ty::Mutability"
              , "crate::lplabel::LPLabel"
              , "crate::maybelabelled::MaybeLabelled" ] }
  , { cratePrefix := "PCG", rustModule := "snapshotlocation"
    , uses := [ "formal_mir::body::BasicBlockIdx" ] }
  , { cratePrefix := "PCG", rustModule := "pcgplace"
    , uses := [ "formal_mir::place::Local"
              , "crate::maybelabelled::MaybeLabelled" ] }
  , { cratePrefix := "PCG", rustModule := "placetriple"
    , uses := [ "formal_mir::place::Place" ] }
  , { cratePrefix := "PCG", rustModule := "transientstate"
    , uses := [ "std::collections::HashSet" ] }
  , { cratePrefix := "PCG"
    , rustModule  := "pcglifetimeprojectionbase"
    , uses := [ "formal_mir::constvalue::ConstValue"
              , "crate::pcgplace::PcgPlace" ] }
  , { cratePrefix := "PCG", rustModule := "capability"
    , items := [Capability.orderDef.toRustPartialOrd] }
  , { cratePrefix := "PCG", rustModule := "validityconditions"
    , uses := [ "formal_mir::body::BasicBlockIdx"
              , "std::collections::HashSet" ]
    , items := [.raw
"pub use formal_runtime::map::*;
pub use formal_runtime::set::*;
"] }
  , { cratePrefix := "OpSem", rustModule := "address"
    , items := [.raw
"impl PartialOrd for Address {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Address {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.addr.cmp(&other.addr)
    }
}
impl std::ops::Add<usize> for Address {
    type Output = Address;
    fn add(self, n: usize) -> Address { Address { addr: self.addr + n } }
}
impl std::ops::Add<&usize> for Address {
    type Output = Address;
    fn add(self, n: &usize) -> Address { Address { addr: self.addr + n } }
}
impl std::ops::Add<usize> for &Address {
    type Output = Address;
    fn add(self, n: usize) -> Address { Address { addr: self.addr + n } }
}
impl std::ops::Add<&usize> for &Address {
    type Output = Address;
    fn add(self, n: &usize) -> Address { Address { addr: self.addr + n } }
}
impl std::ops::Sub<&Address> for &Address {
    type Output = usize;
    fn sub(self, other: &Address) -> usize { self.addr - other.addr }
}
impl std::ops::Sub<Address> for Address {
    type Output = usize;
    fn sub(self, other: Address) -> usize { self.addr - other.addr }
}
impl std::ops::Sub<Address> for &Address {
    type Output = usize;
    fn sub(self, other: Address) -> usize { self.addr - other.addr }
}
impl std::ops::Sub<&Address> for Address {
    type Output = usize;
    fn sub(self, other: &Address) -> usize { self.addr - other.addr }
}
impl PartialEq<&Address> for Address {
    fn eq(&self, other: &&Address) -> bool { self.addr == other.addr }
}
impl PartialEq<Address> for &Address {
    fn eq(&self, other: &Address) -> bool { self.addr == other.addr }
}
impl PartialOrd<&Address> for Address {
    fn partial_cmp(&self, other: &&Address) -> Option<std::cmp::Ordering> { Some(self.addr.cmp(&other.addr)) }
}
impl PartialOrd<Address> for &Address {
    fn partial_cmp(&self, other: &Address) -> Option<std::cmp::Ordering> { Some(self.addr.cmp(&other.addr)) }
}
"] }
  , { cratePrefix := "OpSem", rustModule := "abstractbyte"
    , items := [.raw
"#[allow(non_upper_case_globals)]
pub const uninit: AbstractByte = AbstractByte::Uninit;
"] }
  , { cratePrefix := "OpSem", rustModule := "allocation"
    , items := [.raw "pub use formal_runtime::list::*;\n"] }
  , { cratePrefix := "OpSem", rustModule := "decode"
    , uses := [ "formal_mir::ty::{size_bytes, IntType, \
                 IntValue, Ty}"
              , "formal_mir::constvalue::*" ]
    , items := [.raw
"pub fn encode_le_unsigned(n: &usize, num_bytes: &usize) -> Vec<AbstractByte> {
    let mut out = Vec::with_capacity(*num_bytes);
    let mut cur = *n;
    for _ in 0..*num_bytes {
        out.push(AbstractByte::Init((cur & 0xff) as u8));
        cur >>= 8;
    }
    out
}

pub fn int_value_of_nat(nbytes: &usize, n: &usize) -> Option<IntValue> {
    match *nbytes {
        1 => Some(IntValue::U8(*n as u8)),
        2 => Some(IntValue::U16(*n as u16)),
        4 => Some(IntValue::U32(*n as u32)),
        8 => Some(IntValue::U64(*n as u64)),
        _ => None,
    }
}
"] }
  , { cratePrefix := "OpSem", rustModule := "pointer"
    , uses := [ "formal_mir::ty::Mutability" ] }
  , { cratePrefix := "OpSem", rustModule := "value"
    , uses := [ "formal_mir::ty::*" ] }
  , { cratePrefix := "OpSem", rustModule := "expressions"
    , uses := [ "formal_mir::ty::Ty" ] }
  , { cratePrefix := "OpSem", rustModule := "place"
    , uses := [ "formal_mir::place::*"
              , "formal_mir::ty::Ty" ]
    , items := [.raw "pub use formal_runtime::map::*;\n"] }
  , { cratePrefix := "OpSem", rustModule := "machine"
    , uses := [ "formal_mir::body::*"
              , "formal_mir::constvalue::*"
              , "formal_mir::place::*"
              , "formal_mir::ty::Ty" ]
    , items := [.raw "pub use formal_runtime::map::*;\n"] }
  , { cratePrefix := "OpSem", rustModule := "stackframe"
    , uses := [ "formal_mir::body::*"
              , "formal_mir::place::*" ]
    , items := [.raw "pub use formal_runtime::map::*;\n"] }
  , { cratePrefix := "OpSem", rustModule := "program"
    , uses := [ "formal_mir::body::{Body, valid_body}" ]
    , items := [.raw "pub use formal_runtime::map::*;\n"] }
  , { cratePrefix := "OpSem", rustModule := "layout"
    , uses := [ "formal_mir::ty::*"
              , "formal_mir::issized::is_sized" ] }
  , { cratePrefix := "OpSem", rustModule := "statements"
    , uses := [ "formal_mir::constvalue::ConstValue"
              , "formal_mir::place::Place"
              , "formal_mir::region::Region"
              , "formal_mir::statements::*"
              , "formal_mir::ty::{Mutability, Ty}" ] }
  ]

/-- Build a `RustCrate` from the registry for a given Lean
    module prefix (e.g. `"MIR"` or `"PCG"`). -/
def buildCrate
    (prefix_ : String)
    (enums : List RegisteredEnum)
    (structs : List RegisteredStruct)
    (aliases : List RegisteredAlias)
    (fns : List RegisteredFn)
    (properties : List RegisteredProperty)
    (deps : List RustCrateDep := [])
    (reexports : List String := [])
    (ctx : RustExprCtxt := {})
    : RustCrate :=
  let crateEnums := enums.filter
    (·.leanModule.getRoot.toString == prefix_)
  let crateStructs := structs.filter
    (·.leanModule.getRoot.toString == prefix_)
  let crateAliases := aliases.filter
    (·.leanModule.getRoot.toString == prefix_)
  -- Functions whose body uses constructs the Rust exporter
  -- doesn't (yet) lower faithfully — e.g. passing a
  -- namespaced function as a first-class argument, or
  -- constructing a generic-parameterised struct via its
  -- record-literal shorthand. The Lean and LaTeX versions
  -- remain the authoritative ones until the exporter can
  -- translate these forms itself.
  let rustUnsupported : List (Lean.Name × String) :=
    [(`PCG.BorrowsGraph, "join"),
     (`PCG.Obtain.Tree, "expansionOfStep"),
     (`PCG.Obtain.Tree, "obtainWriteInTree"),
     (`PCG.Obtain.Tree, "obtainWriteInFields"),
     (`PCG.Obtain.Owned, "setOwnedLocalAt"),
     (`PCG.Obtain.Owned, "obtainWriteOwned"),
     (`PCG.Obtain.PcgData, "obtain"),
     (`OpSem.Machine, "stackTail"),
     (`OpSem.Step, "evalStatement"),
     (`OpSem.Terminator, "evalTerminator"),
     (`OpSem.Terminator, "jumpToBlock"),
     (`OpSem.Step, "step"),
     (`OpSem.Terminator, "caseTarget"),
     (`OpSem.Terminator, "evalArgs"),
     (`OpSem.Terminator, "fnFromPtr"),
     (`Properties.Definitions, "pcgAnalysisSucceeds"),
     (`Properties.Definitions, "isInitialState"),
     (`Properties.Soundness, "Soundness")]
  let crateFns := fns.filter fun f =>
    f.leanModule.getRoot.toString == prefix_ &&
      !rustUnsupported.contains
        (f.leanModule, f.fnDef.name)
  let crateProps := properties.filter fun p =>
    p.leanModule.getRoot.toString == prefix_ &&
      !rustUnsupported.contains
        (p.leanModule, p.propertyDef.fnDef.name)
  let crateExtras := extras.filter (·.cratePrefix == prefix_)
  let extraItems : List (String × RustItem) :=
    crateExtras.flatMap fun e =>
      e.items.map fun it => (e.rustModule, it)
  let extraUses : List (String × String) :=
    crateExtras.flatMap fun e =>
      e.uses.map fun u => (e.rustModule, u)
  let crateCtx := { ctx with currentPrefix := prefix_ }
  { name := crateNameOf prefix_
    version := "0.1.0"
    description := s!"Auto-generated {prefix_} types \
      for the PCG formalization."
    edition := "2021"
    crateAttrs := ["allow(unused_parens)",
                   "allow(unreachable_patterns)",
                   "allow(unused_variables)"]
    deps := deps
    reexports := reexports
    modules := buildModules crateEnums crateStructs
      crateAliases crateFns crateProps extraItems extraUses
      crateCtx }

/-- The workspace containing all generated crates. -/
def workspace : RustWorkspace :=
  { members := ["formal-runtime", "formal-mir",
                 "formal-opsem", "formal-pcg"] }

/-- Path-dep on the shared `formal-runtime` crate, added to
    every generated crate so DSL-emitted helper calls
    (`map_empty`, `last`, …) resolve through one source of
    truth. -/
def runtimeDep : RustCrateDep :=
  { name := "formal-runtime", path := "../formal-runtime" }

/-- Write a file, creating parent directories as needed. -/
private def writeFile
    (path : String) (contents : String) : IO Unit := do
  let dir := System.FilePath.mk path |>.parent
    |>.getD (System.FilePath.mk ".")
  IO.FS.createDirAll dir
  IO.FS.writeFile ⟨path⟩ contents
  IO.println s!"  wrote {path}"

/-- Recursively copy every regular file under `srcDir` into
    `dstDir`, preserving relative paths. Used to mirror the
    hand-written `RuntimeRust/` source crate verbatim into
    the generated workspace, analogous to the `Runtime/`
    copy in `LeanExport.main`. Skips build-artefact and
    hidden directories (`target*`, `.git`, etc.). -/
private partial def copyDir
    (srcDir dstDir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll dstDir
  for entry in ← srcDir.readDir do
    let name := entry.fileName
    if name.startsWith "target" || name.startsWith "."
        || name == "Cargo.lock" then
      continue
    let dstEntry := dstDir / name
    if ← entry.path.isDir then
      copyDir entry.path dstEntry
    else
      let contents ← IO.FS.readFile entry.path
      writeFile dstEntry.toString contents

def main (args : List String) : IO Unit := do
  let outDir := args.head? |>.getD "generated/rust"
  let enums ← getRegisteredEnums
  let structs ← getRegisteredStructs
  let aliases ← getRegisteredAliases
  let fns ← getRegisteredFns
  let props ← getRegisteredProperties
  let ctx := buildRustExprCtxt enums structs fns props
  let mirCrate := buildCrate "MIR" enums structs aliases
    fns props (deps := [runtimeDep]) (ctx := ctx)
  let opSemCrate := buildCrate "OpSem" enums structs
    aliases fns props
    (deps := [runtimeDep,
              { name := "formal-mir"
                path := "../formal-mir" }])
    (reexports := ["formal_mir"])
    (ctx := ctx)
  let pcgCrate := buildCrate "PCG" enums structs aliases
    fns props
    (deps := [runtimeDep,
              { name := "formal-mir"
                path := "../formal-mir" }])
    (reexports := ["formal_mir"])
    (ctx := ctx)
  writeFile s!"{outDir}/Cargo.toml" workspace.cargoToml
  -- Mirror the hand-written `RuntimeRust/` crate into the
  -- generated workspace as `formal-runtime/`.
  copyDir "RuntimeRust" s!"{outDir}/formal-runtime"
  for c in [mirCrate, opSemCrate, pcgCrate] do
    for (path, contents) in c.files do
      writeFile s!"{outDir}/{c.name}/{path}" contents
  -- Format the generated Rust code
  let fmtResult ← IO.Process.output {
    cmd := "cargo"
    args := #["fmt", "--all", "--manifest-path",
      s!"{outDir}/Cargo.toml"]
  }
  if fmtResult.exitCode == 0 then
    IO.println "  formatted with cargo fmt"
  else
    IO.eprintln s!"  cargo fmt failed: \
      {fmtResult.stderr}"
  -- Type-check the generated Rust code
  let checkResult ← IO.Process.output {
    cmd := "cargo"
    args := #["check", "--all", "--manifest-path",
      s!"{outDir}/Cargo.toml"]
  }
  if checkResult.exitCode == 0 then
    IO.println "  type-checked with cargo check"
  else
    IO.eprintln s!"  cargo check failed:\n\
      {checkResult.stderr}"
    IO.Process.exit 1
