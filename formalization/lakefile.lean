import Lake
open Lake DSL

package pcg where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
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

lean_exe pcg_export where
  root := `Export
