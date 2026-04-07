import PCG.Capability.Order
import MIR
import OpSem
import Core.Export.Rust
import Core.Dsl.Types.OrderDef

/-- Extra Rust items that cannot be auto-generated from
    `defEnum` / `defStruct` (e.g. trait impls). Keyed by
    `(cratePrefix, rustModuleName)`. -/
def extraItems : List (String × String × RustItem) :=
  [ ("PCG", "capability",
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
")
  , ("OpSem", "decode", .raw
"use formal_mir::ty::Value;
use crate::abstractbyte::AbstractByte::*;
")
  , ("OpSem", "pointer", .raw
"pub fn write_bytes_at(data: &[AbstractByte], offset: &usize, bytes: &[AbstractByte]) -> Vec<AbstractByte> {
    let mut v: Vec<AbstractByte> = data.iter().take(*offset).cloned().collect();
    v.extend(bytes.iter().cloned());
    v.extend(data.iter().skip(*offset + bytes.len()).cloned());
    v
}
pub fn read_bytes_at(data: &[AbstractByte], offset: &usize, len: &usize) -> Vec<AbstractByte> {
    data.iter().skip(*offset).take(*len).cloned().collect()
}
")
  ]

/-- Build a `RustCrate` from the registry for a given Lean
    module prefix (e.g. `"MIR"` or `"PCG"`). -/
def buildCrate
    (prefix_ : String)
    (enums : List RegisteredEnum)
    (structs : List RegisteredStruct)
    (fns : List RegisteredFn)
    (properties : List RegisteredProperty)
    (deps : List RustCrateDep := [])
    (reexports : List String := [])
    : RustCrate :=
  let crateEnums := enums.filter
    (·.leanModule.getRoot.toString == prefix_)
  let crateStructs := structs.filter
    (·.leanModule.getRoot.toString == prefix_)
  let crateFns := fns.filter
    (·.leanModule.getRoot.toString == prefix_)
  let crateProps := properties.filter
    (·.leanModule.getRoot.toString == prefix_)
  let extras := extraItems.filterMap fun (p, m, item) =>
    if p == prefix_ then some (m, item) else none
  { name := crateNameOf prefix_
    version := "0.1.0"
    description := s!"Auto-generated {prefix_} types \
      for the PCG formalization."
    edition := "2021"
    crateAttrs := ["allow(unused_parens)"]
    deps := deps
    reexports := reexports
    modules := buildModules crateEnums crateStructs
      crateFns crateProps extras }

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
  let fns ← getRegisteredFns
  let props ← getRegisteredProperties
  let mirCrate := buildCrate "MIR" enums structs fns
    props
  let opSemCrate := buildCrate "OpSem" enums structs fns
    props
    (deps := [{ name := "formal-mir"
                path := "../formal-mir" }])
    (reexports := ["formal_mir"])
  let pcgCrate := buildCrate "PCG" enums structs fns
    props
    (deps := [{ name := "formal-mir"
                path := "../formal-mir" }])
    (reexports := ["formal_mir"])
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
