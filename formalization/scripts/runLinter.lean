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

/-- Whether a name is a compiler-generated auxiliary
    (match equational lemmas, sizeof specs, etc.). -/
private def isAuxDecl : Name → Bool
  | .str _ s =>
    s.startsWith "eq_" ||
    s.startsWith "match_" ||
    s.startsWith "proof_" ||
    s.endsWith "sizeOf_spec" ||
    s.endsWith "_sunfold" ||
    s == "splitter" ||
    s == "recOn" || s == "casesOn" ||
    s == "noConfusion" || s == "noConfusionType" ||
    s == "toCtorIdx" || s == "ctorIdx" ||
    s == "elim" || s == "brecOn" || s == "below" ||
    s == "ndrec" || s == "ndrecOn" ||
    s == "binductionOn" || s == "rec" ||
    s == "_unsafe_rec" || s == "_unary"
  | .num p _ => isAuxDecl p
  | _ => false

/-- Check for unused private declarations in a module.
    A private declaration is unused if no other declaration
    in the package references it. -/
def unusedPrivateLint
    (env : Environment) (decls : Array Name)
    : CoreM (Std.HashMap Name MessageData) := do
  -- Collect the set of all constants referenced by
  -- non-private declarations (and other private ones)
  let mut referenced : NameSet := {}
  for d in decls do
    if let some ci := env.find? d then
      for c in ci.getUsedConstantsAsSet do
        -- Exclude self-references
        if c != d then
          referenced := referenced.insert c
  -- Find private declarations not referenced by anyone
  let mut results : Std.HashMap Name MessageData := {}
  for d in decls do
    if !isPrivateName d then continue
    if d.hasMacroScopes then continue
    if ← isProjectionFn d then continue
    if env.isConstructor d then continue
    -- Skip compiler-generated auxiliaries
    if isAuxDecl d then continue
    if !referenced.contains d then
      results := results.insert d
        m!"private declaration is never referenced"
  return results

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
      -- Run custom unused-private lint
      let unusedPrivateResults ←
        unusedPrivateLint (← getEnv) decls
      let unusedPrivateLinter : NamedLinter :=
        { name := `unusedPrivate
          declName := `unusedPrivate
          test := fun _ => pure none
          noErrorsFound :=
            "No unused private declarations."
          errorsFound :=
            "UNUSED PRIVATE DECLARATIONS:" }
      let allResults := if unusedPrivateResults.isEmpty
        then results
        else results.push
          (unusedPrivateLinter, unusedPrivateResults)
      let failed := allResults.any (!·.2.isEmpty)
      if failed then
        anyFailed := true
        let fmtResults ← formatLinterResults allResults
          decls (groupByFilename := true)
          (useErrorFormat := true)
          s!"in {mod}" (runSlowLinters := true)
          .medium (linters.size + 1)
        IO.print (← fmtResults.toString)
      else
        IO.println s!"-- Linting passed for {mod}."
    if anyFailed then IO.Process.exit 1
    IO.Process.exit 0
