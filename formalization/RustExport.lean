import PCG.Capability.Order
import MIR.Ty
import Shared.Rust
import Shared.OrderDef

/-- Extra Rust items that cannot be auto-generated from
    `defEnum` / `defStruct` (e.g. trait impls). Keyed by
    `(cratePrefix, rustModuleName)`. -/
def extraItems : List (String × String × RustItem) :=
  [ ("PCG", "capability",
     Capability.orderDef.toRustPartialOrd) ]

/-- Build a `RustCrate` from the registry for a given Lean
    module prefix (e.g. `"MIR"` or `"PCG"`). -/
def buildCrate
    (prefix_ : String)
    (enums : List RegisteredEnum)
    (structs : List RegisteredStruct)
    (fns : List RegisteredFn)
    (deps : List RustCrateDep := [])
    (reexports : List String := [])
    : RustCrate :=
  let crateEnums := enums.filter
    (·.leanModule.getRoot.toString == prefix_)
  let crateStructs := structs.filter
    (·.leanModule.getRoot.toString == prefix_)
  let crateFns := fns.filter
    (·.leanModule.getRoot.toString == prefix_)
  let extras := extraItems.filterMap fun (p, m, item) =>
    if p == prefix_ then some (m, item) else none
  { name := crateNameOf prefix_
    version := "0.1.0"
    description := s!"Auto-generated {prefix_} types \
      for the PCG formalization."
    edition := "2021"
    deps := deps
    reexports := reexports
    modules := buildModules crateEnums crateStructs
      crateFns extras }

/-- The workspace containing all generated crates. -/
def workspace : RustWorkspace :=
  { members := ["formal-mir", "formal-pcg"] }

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
  let mirCrate := buildCrate "MIR" enums structs fns
  let pcgCrate := buildCrate "PCG" enums structs fns
    (deps := [{ name := "formal-mir"
                path := "../formal-mir" }])
    (reexports := ["formal_mir"])
  writeFile s!"{outDir}/Cargo.toml" workspace.cargoToml
  for c in [mirCrate, pcgCrate] do
    for (path, contents) in c.files do
      writeFile s!"{outDir}/{c.name}/{path}" contents
