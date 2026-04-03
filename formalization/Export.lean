import PCG.Capability
import Shared.Rust

def main : IO Unit := do
  let d := Capability.enumDef

  IO.println "=== Short definition (LaTeX) ==="
  IO.println d.shortDef.toLaTeX
  IO.println ""

  IO.println "=== Short definition (Typst) ==="
  IO.println d.shortDef.toTypst
  IO.println ""

  IO.println "=== Short definition (HTML) ==="
  IO.println d.shortDef.toHTML
  IO.println ""

  IO.println "=== Long definition (LaTeX) ==="
  IO.println d.longDef.toLaTeX
  IO.println ""

  IO.println "=== Rust ==="
  IO.println d.toRust
