import PCG.Capability

def main : IO Unit := do
  IO.println "=== Rust ==="
  IO.println Capability.enumDef.toRust
  IO.println ""
  IO.println "=== LaTeX ==="
  IO.println Capability.enumDef.toLaTeX
