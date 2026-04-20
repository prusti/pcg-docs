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
import Core.Export.Rust
import Core.Dsl.Types.OrderDef

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
  , ("PCG", "snapshotlocation", .raw
"use formal_mir::body::BasicBlockIdx;
")
  , ("PCG", "pcgplace", .raw
"use formal_mir::place::Local;
use crate::maybelabelledplace::MaybeLabelledPlace;
")
  , ("PCG", "capability",
     Capability.orderDef.toRustPartialOrd)
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
"use formal_mir::ty::{size_bytes, IntType, IntValue, Size, Ty};
use formal_mir::constvalue::*;
use crate::abstractbyte::AbstractByte::*;
use crate::value::*;

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
use crate::value::*;
")
  , ("OpSem", "statements", .raw
"use formal_mir::ty::Ty;
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
  let crateFns := fns.filter
    (·.leanModule.getRoot.toString == prefix_)
  let crateProps := properties.filter
    (·.leanModule.getRoot.toString == prefix_)
  let extras := extraItems.filterMap fun (p, m, item) =>
    if p == prefix_ then some (m, item) else none
  let crateCtx := { ctx with currentPrefix := prefix_ }
  { name := crateNameOf prefix_
    version := "0.1.0"
    description := s!"Auto-generated {prefix_} types \
      for the PCG formalization."
    edition := "2021"
    crateAttrs := ["allow(unused_parens)",
                   "allow(unreachable_patterns)"]
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
