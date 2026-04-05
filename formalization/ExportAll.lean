/-! Run all export targets: Lean, Rust, and LaTeX. -/

private def runExport (name : String)
    (args : List String := []) : IO Unit := do
  IO.println s!"── {name} ──"
  let result ← IO.Process.output {
    cmd := "lake"
    args := #["exe", name] ++ args.toArray
  }
  IO.print result.stdout
  if result.exitCode != 0 then
    IO.eprint result.stderr
    throw <| IO.userError s!"{name} failed"

def main (args : List String) : IO Unit := do
  runExport "lean_export" args
  runExport "rust_export" args
  runExport "presentation_export" args
  IO.println "── all exports succeeded ──"
