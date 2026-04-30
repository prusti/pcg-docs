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

/-- Extra Rust items that cannot be auto-generated from
    `defEnum` / `defStruct` (e.g. trait impls). Keyed by
    `(cratePrefix, rustModuleName)`. -/
def extraItems : List (String × String × RustItem) :=
  [ ("PCG", "borrowchecker", .raw
"use formal_mir::body::Location;
use crate::pcgnode::PcgNode;
")
  , ("PCG", "analysislocation", .raw
"use formal_mir::body::Location;
")
  , ("PCG", "analysisobject", .raw
"use formal_mir::body::Terminator;
use formal_mir::statements::Statement;
")
  , ("PCG", "borrowedge", .raw
"use formal_mir::body::Location;
use formal_mir::region::Region;
use formal_mir::ty::Mutability;
use crate::lifetimeprojectionlabel::LifetimeProjectionLabel;
use crate::maybelabelled::MaybeLabelled;
")
  , ("PCG", "snapshotlocation", .raw
"use formal_mir::body::BasicBlockIdx;
")
  , ("PCG", "pcgplace", .raw
"use formal_mir::place::Local;
use crate::maybelabelled::MaybeLabelled;
")
  , ("PCG", "placetriple", .raw
"use formal_mir::place::Place;
")
  , ("PCG", "transientstate", .raw
"use std::collections::HashSet;
")
  , ("PCG", "pcglifetimeprojectionbase", .raw
"use formal_mir::constvalue::ConstValue;
use crate::pcgplace::PcgPlace;
")
  , ("PCG", "capability",
     Capability.orderDef.toRustPartialOrd)
  , ("PCG", "validityconditions", .raw
"use formal_mir::body::BasicBlockIdx;
use std::collections::HashSet;

pub fn map_empty<K: Eq + std::hash::Hash, V>() -> HashMap<K, V> {
    HashMap::new()
}

pub fn map_singleton<K: Eq + std::hash::Hash, V>(k: &K, v: &V)
    -> HashMap<K, V>
where K: Clone, V: Clone {
    let mut m = HashMap::new();
    m.insert(k.clone(), v.clone());
    m
}

pub fn map_union_sets<
    K: Eq + std::hash::Hash + Clone,
    T: Eq + std::hash::Hash + Clone,
>(
    m1: &HashMap<K, HashSet<T>>,
    m2: &HashMap<K, HashSet<T>>,
) -> HashMap<K, HashSet<T>> {
    let mut out: HashMap<K, HashSet<T>> = m1.clone();
    for (k, v) in m2.iter() {
        out.entry(k.clone())
            .and_modify(|e| e.extend(v.iter().cloned()))
            .or_insert_with(|| v.clone());
    }
    out
}

pub fn set_singleton<T: Eq + std::hash::Hash + Clone>(x: &T)
    -> HashSet<T> {
    let mut s = HashSet::new();
    s.insert(x.clone());
    s
}
")
  , ("OpSem", "address", .raw
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
")
  , ("OpSem", "abstractbyte", .raw
"#[allow(non_upper_case_globals)]
pub const uninit: AbstractByte = AbstractByte::Uninit;
")
  , ("OpSem", "allocation", .raw
"pub fn last<T: Clone>(xs: &[T]) -> Option<T> { xs.last().cloned() }
pub fn replicate<T: Clone>(n: &usize, x: &T) -> Vec<T> { vec![x.clone(); *n] }
pub fn list_set<T: Clone>(xs: &[T], i: &usize, x: &T) -> Vec<T> {
    let mut v: Vec<T> = xs.to_vec();
    if *i < v.len() { v[*i] = x.clone(); }
    v
}
pub fn list_take<T: Clone>(n: &usize, xs: &[T]) -> Vec<T> {
    xs.iter().take(*n).cloned().collect()
}
pub fn list_drop<T: Clone>(n: &usize, xs: &[T]) -> Vec<T> {
    xs.iter().skip(*n).cloned().collect()
}
")
  , ("OpSem", "decode", .raw
"use formal_mir::ty::{size_bytes, IntType, IntValue, Ty};
use formal_mir::constvalue::*;

pub fn encode_le_unsigned(n: &usize, num_bytes: &usize) -> Vec<AbstractByte> {
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
")
  , ("OpSem", "pointer", .raw
"use formal_mir::ty::Mutability;
")
  , ("OpSem", "value", .raw
"use formal_mir::ty::*;
")
  , ("OpSem", "expressions", .raw
"use formal_mir::ty::Ty;
")
  , ("OpSem", "place", .raw
"use formal_mir::place::*;
use formal_mir::ty::Ty;

pub fn map_get<'a, K: Eq + std::hash::Hash, V>(m: &'a std::collections::HashMap<K, V>, k: &K) -> Option<&'a V> {
    m.get(k)
}
")
  , ("OpSem", "machine", .raw
"use formal_mir::body::*;
use formal_mir::constvalue::*;
use formal_mir::place::*;
use formal_mir::ty::Ty;

pub fn map_empty<K: Eq + std::hash::Hash, V>()
    -> std::collections::HashMap<K, V> {
    std::collections::HashMap::new()
}
")
  , ("OpSem", "stackframe", .raw
"use formal_mir::body::*;
use formal_mir::place::*;

pub fn map_insert<K: Eq + std::hash::Hash + Clone, V: Clone>(
    m: &std::collections::HashMap<K, V>, k: &K, v: &V,
) -> std::collections::HashMap<K, V> {
    let mut out = m.clone();
    out.insert(k.clone(), v.clone());
    out
}

pub fn map_remove<K: Eq + std::hash::Hash + Clone, V: Clone>(
    m: &std::collections::HashMap<K, V>, k: &K,
) -> std::collections::HashMap<K, V> {
    let mut out = m.clone();
    out.remove(k);
    out
}
")
  , ("OpSem", "program", .raw
"use formal_mir::body::Body;

pub fn map_at<K: Eq + std::hash::Hash, V: Clone>(
    m: &std::collections::HashMap<K, V>, k: &K,
) -> V {
    m[k].clone()
}
")
  , ("OpSem", "layout", .raw
"use formal_mir::ty::*;
use formal_mir::issized::is_sized;
")
  , ("OpSem", "statements", .raw
"use formal_mir::constvalue::ConstValue;
use formal_mir::place::Place;
use formal_mir::region::Region;
use formal_mir::statements::*;
use formal_mir::ty::{Mutability, Ty};
")
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
     (`OpSem.Step, "evalTerminator"),
     (`OpSem.Step, "jumpToBlock"),
     (`OpSem.Step, "step"),
     (`OpSem.Step, "caseTarget"),
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
  let extras := extraItems.filterMap fun (p, m, item) =>
    if p == prefix_ then some (m, item) else none
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
      crateAliases crateFns crateProps extras crateCtx }

/-- The workspace containing all generated crates. -/
def workspace : RustWorkspace :=
  { members := ["formal-mir", "formal-opsem",
                 "formal-pcg"] }

/-- Write a file, creating parent directories as needed. -/
private def writeFile
    (path : String) (contents : String) : IO Unit := do
  let dir := System.FilePath.mk path |>.parent
    |>.getD (System.FilePath.mk ".")
  IO.FS.createDirAll dir
  IO.FS.writeFile ⟨path⟩ contents
  IO.println s!"  wrote {path}"

def main (args : List String) : IO Unit := do
  let outDir := args.head? |>.getD "generated/rust"
  let enums ← getRegisteredEnums
  let structs ← getRegisteredStructs
  let aliases ← getRegisteredAliases
  let fns ← getRegisteredFns
  let props ← getRegisteredProperties
  let ctx := buildRustExprCtxt enums structs fns props
  let mirCrate := buildCrate "MIR" enums structs aliases
    fns props (ctx := ctx)
  let opSemCrate := buildCrate "OpSem" enums structs
    aliases fns props
    (deps := [{ name := "formal-mir"
                path := "../formal-mir" }])
    (reexports := ["formal_mir"])
    (ctx := ctx)
  let pcgCrate := buildCrate "PCG" enums structs aliases
    fns props
    (deps := [{ name := "formal-mir"
                path := "../formal-mir" }])
    (reexports := ["formal_mir"])
    (ctx := ctx)
  writeFile s!"{outDir}/Cargo.toml" workspace.cargoToml
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
