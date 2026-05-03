import Core.Registry
import Lean

/-- `registerPresentation <expr>` records a `Presentation`
    value in the global presentation registry, tagged with the
    module currently being elaborated. It is the conventional
    way to make a template presentation visible to the
    presentation exporter:

    ```
    def myTemplate : Presentation := { … }
    registerPresentation myTemplate
    ```

    The wrapper exists to spare callers from having to write
    out the surrounding `initialize` block and the literal
    `Lean.Name` of their own module. -/
syntax "registerPresentation " term : command

open Lean Elab Command in
elab_rules : command
  | `(registerPresentation $p:term) => do
    let mod ← getMainModule
    let modName : TSyntax `term := quote mod
    elabCommand (← `(command|
      initialize registerPresentationDef ($p : Presentation) $modName))
