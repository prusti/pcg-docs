import Lake
open Lake DSL

package pcg where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`linter.all, true⟩,
    ⟨`linter.missingDocs, false⟩
  ]

require batteries from
  git "https://github.com/leanprover-community/batteries"
    @ "main"

require LSpec from
  git "https://github.com/argumentcomputer/LSpec"
    @ "main"

@[default_target]
lean_lib Runtime where
  srcDir := "."

@[default_target]
lean_lib Core where
  srcDir := "."

@[default_target]
lean_lib MIR where
  srcDir := "."

@[default_target]
lean_lib PCG where
  srcDir := "."

@[default_target]
lean_lib OpSem where
  srcDir := "."

-- The Properties library bridges PCG and OpSem. Its
-- submodules house the supporting definitions and the analysis
-- properties (aliasing, soundness) that combine the two
-- otherwise-independent halves of the formalization.
@[default_target]
lean_lib Properties where
  srcDir := "."

@[default_target]
lean_lib Presentation where
  srcDir := "."

lean_exe rust_export where
  root := `RustExport

lean_exe presentation_export where
  root := `PresentationExport

lean_exe lean_export where
  root := `LeanExport

lean_exe export_all where
  root := `ExportAll

@[default_target]
lean_lib Tests where
  srcDir := "."

@[test_driver]
lean_exe tests where
  root := `Tests

@[lint_driver]
lean_exe runLinter where
  srcDir := "scripts"
  root := `runLinter
  supportInterpreter := true

lean_exe check_banned_patterns where
  srcDir := "scripts"
  root := `CheckBannedPatterns
  supportInterpreter := true
