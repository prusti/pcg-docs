import PCG.Capability.Order
import MIR.Region
import Shared.Rust
import Shared.OrderDef


/-- Build a tuple struct item from a doc string, name, and
    list of `(visibility, type)` fields. -/
private def mkTupleStruct
    (doc : String) (name : String)
    (fields : List (RustVis × String))
    : RustItem :=
  .tupleStruct doc [.derive defaultRustDerives]
    .pub name fields

/-- The MIR types crate. -/
def mirCrate : RustCrate :=
  let regVid := mkTupleStruct
    "A region variable identifier." "RegionVid"
    [(.pub, "usize")]
  let earlyBound := mkTupleStruct
    "An early-bound region index." "EarlyBoundRegion"
    [(.pub, "usize")]
  { name := "mir-types"
    version := "0.1.0"
    description :=
      "Auto-generated MIR types for the PCG formalization."
    edition := "2021"

    modules :=
      [ { name := "region"
          doc := Region.enumDef.doc
          items :=
            [ regVid
            , earlyBound
            , Region.enumDef.toRustItem ] } ] }

/-- The PCG types crate (depends on `mir-types`). -/
def pcgCrate : RustCrate :=
  { name := "pcg-types"
    version := "0.1.0"
    description :=
      "Auto-generated PCG types for the PCG formalization."
    edition := "2021"

    deps := [{ name := "mir-types"
               path := "../mir-types" }]
    reexports := ["mir_types"]
    modules :=
      [ { name := "capability"
          doc := Capability.enumDef.doc
          items :=
            [ Capability.enumDef.toRustItem
            , Capability.orderDef.toRustPartialOrd
            ] } ] }

/-- The workspace containing both crates. -/
def workspace : RustWorkspace :=
  { members := ["mir-types", "pcg-types"] }

/-- Write a file, creating parent directories as needed. -/
private def writeFile (path : String) (contents : String)
    : IO Unit := do
  let dir := System.FilePath.mk path |>.parent
    |>.getD (System.FilePath.mk ".")
  IO.FS.createDirAll dir
  IO.FS.writeFile ⟨path⟩ contents
  IO.println s!"  wrote {path}"

def main (args : List String) : IO Unit := do
  let outDir := args.head? |>.getD "generated/rust"
  writeFile s!"{outDir}/Cargo.toml" workspace.cargoToml
  let crates := [mirCrate, pcgCrate]
  for c in crates do
    for (path, contents) in c.files do
      writeFile s!"{outDir}/{c.name}/{path}" contents
