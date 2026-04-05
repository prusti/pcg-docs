import Lake
open Lake DSL

package pcg where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`linter.all, true⟩,
    ⟨`linter.missingDocs, false⟩
  ]

@[default_target]
lean_lib Shared where
  srcDir := "."

@[default_target]
lean_lib MIR where
  srcDir := "."

@[default_target]
lean_lib PCG where
  srcDir := "."

lean_exe rust_export where
  root := `RustExport

lean_exe presentation_export where
  root := `PresentationExport
