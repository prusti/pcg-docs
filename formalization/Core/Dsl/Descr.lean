import Core.Registry
import Lean

/-- `descr <doc>` registers a free-form `Doc` description
    in the current module. In the presentation export the
    description is rendered to LaTeX and included at that
    position within its module's body. -/
syntax "descr " term : command

open Lean Elab Command in
elab_rules : command
  | `(descr $doc:term) => do
    let mod ← getMainModule
    let modName : TSyntax `term := quote mod
    elabCommand (← `(command|
      initialize registerDescr ($doc : Doc) $modName))
