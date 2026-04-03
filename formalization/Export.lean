import PCG.Capability
import Shared.Rust

/-- The generated Rust crate containing all PCG definitions. -/
def pcgCrate : RustCrate :=
  { name := "pcg-types"
    version := "0.1.0"
    description := "Auto-generated types for the PCG formalization."
    edition := "2021"
    modules :=
      [ { name := "capability"
          doc := Capability.enumDef.doc
          items := [Capability.enumDef.toRustItem] } ] }

def main (args : List String) : IO Unit := do
  let outDir := args.head? |>.getD "generated/rust"
  for (path, contents) in pcgCrate.files do
    let fullPath := s!"{outDir}/{path}"
    let dir := System.FilePath.mk fullPath |>.parent
      |>.getD (System.FilePath.mk ".")
    IO.FS.createDirAll dir
    IO.FS.writeFile ⟨fullPath⟩ contents
    IO.println s!"  wrote {fullPath}"
