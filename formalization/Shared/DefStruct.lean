import Shared.Registry
import Lean

open Lean in

declare_syntax_cat structField

/-- A field in a `defStruct` declaration:
    `| name "doc" : Type`. -/
syntax "| " ident str ":" term : structField

/-- Define a structure with cross-language export metadata.

    Generates:
    1. A Lean `structure` with derived instances
    2. A `.structDef : StructDef` for export

    Example:
    ```
    defStruct RegionVid (.text "vid")
      "A region variable identifier."
    where
      | id "The region variable id." : Nat
    ``` -/
syntax "defStruct " ident "(" term ")" str " where"
    structField* ("deriving " ident,+)? : command

/-- Extract field name, type, and doc from a `structField`
    syntax node. -/
private def parseStructField
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM
        (Lean.Ident × Lean.Syntax
         × Lean.TSyntax `str) := do
  match stx with
  | `(structField| | $n:ident $d:str : $t:term) =>
    pure (n, t, d)
  | _ => Lean.Elab.throwUnsupportedSyntax

open Lean Elab Command in
elab_rules : command
  | `(defStruct $name:ident ($symDoc:term)
       $doc:str where
       $fs:structField* $[deriving $derivs:ident,*]?)
    => do
    let fieldData ← fs.mapM parseStructField
    -- Build the structure definition as a string and
    -- parse it, avoiding manual syntax construction.
    let fieldStrs := fieldData.map fun (fn, ft, _) =>
      let typeStr :=
        if ft.isIdent then toString ft.getId
        else ft.reprint.getD (toString ft)
      s!"  {fn.getId} : {typeStr}"
    let structStr :=
      s!"structure {name.getId} where\n\
         {"\n".intercalate fieldStrs.toList}"
    let env ← getEnv
    match Parser.runParserCategory env `command
      structStr with
    | .ok stx => elabCommand stx
    | .error e =>
      throwError s!"defStruct: parse error: {e}\n\
        ---\n{structStr}\n---"
    let deriveNames : Array Ident := match derivs with
      | some ds => ds
      | none =>
        #[mkIdent `DecidableEq, mkIdent `Repr]
    for d in deriveNames do
      elabCommand (← `(command|
        deriving instance $d:ident for $name))
    -- Build StructDef metadata
    let fieldDefs ← fieldData.mapM
      fun (fn, ft, fd) => do
        let ns : TSyntax `term :=
          quote (toString fn.getId)
        let typeStr :=
          if ft.isIdent then toString ft.getId
          else ft.reprint.getD (toString ft)
        let tyTerm ← `(FType.parse $(quote typeStr))
        `({ name := $ns, ty := $tyTerm,
            doc := $fd : FieldDef })
    let ns : TSyntax `term :=
      quote (toString name.getId)
    let fieldList ← `([$[$fieldDefs],*])
    elabCommand (← `(command|
      def $(mkIdent (name.getId ++ `structDef))
          : StructDef :=
        { name := $ns,
          symbolDoc := ($symDoc : Doc), doc := $doc,
          fields := $fieldList }))
    let mod ← getMainModule
    let modName : TSyntax `term := quote mod
    let sdId := mkIdent (name.getId ++ `structDef)
    elabCommand (← `(command|
      initialize registerStructDef $sdId $modName))
