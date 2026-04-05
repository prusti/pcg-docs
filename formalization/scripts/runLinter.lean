import Batteries.Tactic.Lint

open Lean Elab Command Batteries.Tactic.Lint

/-- Linters to exclude from the default set. -/
def excludedLinters : List Name := [
  `docBlame
]

/-- Run all default linters except excluded ones on
    the given modules. -/
unsafe def main (args : List String) : IO Unit := do
  let modules := args.map String.toName
  if modules.isEmpty then
    IO.eprintln "Usage: runLinter Module1 Module2 ..."
    IO.Process.exit 1
  initSearchPath (← findSysroot)
  enableInitializersExecution
  for mod in modules do
    let env ← importModules
      #[mod, `Batteries.Tactic.Lint] {}
      (trustLevel := 1024) (loadExts := true)
    let ctx : Core.Context :=
      { fileName := "", fileMap := default }
    let state : Core.State := { env }
    Prod.fst <$> (Core.CoreM.toIO · ctx state) do
      let decls ← getDeclsInPackage mod.getRoot
      let allLinters ← getChecks
        (slow := true) (runAlways := none)
        (runOnly := none)
      let linters := allLinters.filter fun
        (l : NamedLinter) =>
        !excludedLinters.contains l.name
      let results ← lintCore decls linters
      let failed := results.any (!·.2.isEmpty)
      if failed then
        let fmtResults ← formatLinterResults results
          decls (groupByFilename := true)
          (useErrorFormat := true)
          s!"in {mod}" (runSlowLinters := true)
          .medium linters.size
        IO.print (← fmtResults.toString)
        IO.Process.exit 1
      else
        IO.println s!"-- Linting passed for {mod}."
  IO.Process.exit 0
