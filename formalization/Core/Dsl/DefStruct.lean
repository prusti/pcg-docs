import Core.Registry
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
    defStruct RegionVid (.doc (.plain "vid"),
        .doc (.plain "RegionVid"))
      "Region Variables"
      "A region variable identifier."
    where
      | id "The region variable id." : Nat
    ``` -/
syntax "defStruct " ident ("{" ident+ "}")?
    "(" term "," term ")"
    str str ("constructor" str)? ("note" str)? ("link" str)?
    " where"
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
  | `(defStruct $name:ident $[{ $tps:ident* }]?
       ($symDoc:term, $setDoc:term)
       $docParam:str $doc:str $[constructor $ctorName:str]?
       $[note $noteLit:str]? $[link $linkLit:str]? where
       $fs:structField* $[deriving $derivs:ident,*]?)
    => do
    let fieldData ← fs.mapM parseStructField
    let typeParamNames : List String := match tps with
      | some ids => ids.toList.map (toString ·.getId)
      | none => []
    let isGeneric := !typeParamNames.isEmpty
    -- Build the structure definition as a string and
    -- parse it, avoiding manual syntax construction.
    let fieldStrs := fieldData.map fun (fn, ft, _) =>
      let typeStr :=
        if ft.isIdent then toString ft.getId
        else ft.reprint.getD (toString ft)
      s!"  {fn.getId} : {typeStr}"
    let tpStr :=
      if typeParamNames.isEmpty then ""
      else " " ++ " ".intercalate
        (typeParamNames.map fun p => s!"\{{p} : Type}")
    -- Generic structs embed `deriving` inside the
    -- structure declaration; the separate `deriving
    -- instance` commands below only handle monomorphic
    -- types.
    let inlineDeriving :=
      if isGeneric then "\n  deriving DecidableEq, Repr, Hashable"
      else ""
    let structStr :=
      s!"structure {name.getId}{tpStr} where\n\
         {"\n".intercalate fieldStrs.toList}\
         {inlineDeriving}"
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
        #[mkIdent `DecidableEq, mkIdent `Repr,
          mkIdent `Hashable]
    unless isGeneric do
      for d in deriveNames do
        elabCommand (← `(command|
          deriving instance $d:ident for $name))
    -- Build StructDef metadata
    let selfN := Name.mkSimple (toString name.getId)
    let fieldDefs ← fieldData.mapM
      fun (fn, ft, fd) => do
        let ns : TSyntax `term :=
          quote (toString fn.getId)
        let typeStr :=
          if ft.isIdent then toString ft.getId
          else ft.reprint.getD (toString ft)
        let tyTerm ← `(DSLType.parse $(quote typeStr))
        let symTerm : TSyntax `term ←
          if ft.isIdent then do
            let tn := Name.mkSimple (toString ft.getId)
            let env ← getEnv
            if tn == selfN then
              `(some ($symDoc : MathDoc))
            else if env.find? (tn ++ `enumDef) |>.isSome
                then
              let ref := mkIdent
                (tn ++ `enumDef ++ `symbolDoc)
              `(some $ref)
            else if env.find? (tn ++ `structDef)
                |>.isSome then
              let ref := mkIdent
                (tn ++ `structDef ++ `symbolDoc)
              `(some $ref)
            else `(none)
          else `(none)
        `({ name := $ns, ty := $tyTerm,
            doc := $fd,
            symbolDoc := $symTerm : FieldDef })
    let ns : TSyntax `term :=
      quote (toString name.getId)
    let fieldList ← `([$[$fieldDefs],*])
    let ctorTerm : TSyntax `term ← match ctorName with
      | some cn => `(some $cn)
      | none => `(none)
    let noteTerm : TSyntax `term ← match noteLit with
      | some n => `(some $n)
      | none => `(none)
    let linkTerm : TSyntax `term ← match linkLit with
      | some l => `(some $l)
      | none => `(none)
    let sdId := mkIdent (name.getId ++ `structDef)
    let typeParamsTerm : TSyntax `term :=
      quote typeParamNames
    elabCommand (← `(command|
      def $sdId : StructDef :=
        { name := $ns,
          symbolDoc := ($symDoc : MathDoc),
          setDoc := ($setDoc : MathDoc),
          docParam := $docParam,
          doc := Doc.interpolateDef $doc
            ($symDoc : MathDoc) ($setDoc : MathDoc),
          ctorName := $ctorTerm,
          «note» := $noteTerm,
          «link» := $linkTerm,
          typeParams := $typeParamsTerm,
          fields := $fieldList }))
    let mod ← getMainModule
    let modName : TSyntax `term := quote mod
    elabCommand (← `(command|
      initialize registerStructDef $sdId $modName))
