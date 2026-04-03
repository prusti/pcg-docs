import Lake
open Lake DSL

package pcg where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib MIR where
  srcDir := "."

@[default_target]
lean_lib PCG where
  srcDir := "."
