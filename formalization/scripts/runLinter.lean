import Batteries.Tactic.Lint

open Lean Elab Command Batteries.Tactic.Lint

/-- Linters to exclude from the default set. -/
def excludedLinters : List Name := [
  `docBlame
]

/-- Whether a declaration is an auto-derived Repr
    instance (produces false-positive unusedArguments). -/
def isDerivedRepr (n : Name) : Bool :=
  n.toString.startsWith "instRepr"

/-- Run all default linters except excluded ones on
    the given modules. -/
unsafe def main (args : List String) : IO Unit := do
  let modules := args.map String.toName
  if modules.isEmpty then
    IO.eprintln "Usage: runLinter Module1 Module2 ..."
    IO.Process.exit 1
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let imports := (modules ++ [`Batteries.Tactic.Lint]).map
    fun m => ({ module := m } : Import)
  let env ← importModules imports.toArray {}
    (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context :=
    { fileName := "", fileMap := default }
  let state : Core.State := { env }
  Prod.fst <$> (Core.CoreM.toIO · ctx state) do
    let allLinters ← getChecks
      (slow := true) (runAlways := none)
      (runOnly := none)
    let linters := allLinters.filter fun
      (l : NamedLinter) =>
      !excludedLinters.contains l.name
    let mut anyFailed := false
    for mod in modules do
      let decls ← getDeclsInPackage mod.getRoot
      let results ← lintCore decls linters
      let results := results.map fun (linter, hm) =>
        if linter.name == `unusedArguments then
          let hm' := hm.fold
            (init := ({} : Std.HashMap Name MessageData))
            fun acc n msg =>
              if isDerivedRepr n then acc
              else acc.insert n msg
          (linter, hm')
        else (linter, hm)
      let failed := results.any (!·.2.isEmpty)
      if failed then
        anyFailed := true
        let fmtResults ← formatLinterResults results
          decls (groupByFilename := true)
          (useErrorFormat := true)
          s!"in {mod}" (runSlowLinters := true)
          .medium linters.size
        IO.print (← fmtResults.toString)
      else
        IO.println s!"-- Linting passed for {mod}."
    if anyFailed then IO.Process.exit 1
    IO.Process.exit 0
