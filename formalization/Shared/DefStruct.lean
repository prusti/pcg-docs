import Shared.Registry
import Lean

open Lean in

declare_syntax_cat structField

/-- A field in a `defStruct` declaration:
    `| name "doc" : Type`. -/
syntax "| " ident str ":" term : structField

/-- Define a structure with cross-language export metadata.

    Generates:
    1. A Lean `structure` with `DecidableEq` and `Repr`
    2. A `.structDef : StructDef` for export

    Example:
    ```
    defStruct RegionVid (.text "vid")
      "A region variable identifier."
    where
      | id "The region variable id." : Nat
    ```
    produces `structure RegionVid` and
    `RegionVid.structDef`. -/
syntax "defStruct " ident "(" term ")" str " where"
    structField* ("deriving " ident,+)? : command

private def mkNullNode' : Lean.Syntax :=
  Lean.Syntax.node .none `null #[]

private def mkEmptyDeclModifiers : Lean.Syntax :=
  Lean.Syntax.node .none ``Lean.Parser.Command.declModifiers
    #[mkNullNode', mkNullNode', mkNullNode',
      mkNullNode', mkNullNode', mkNullNode', mkNullNode']

/-- Build a `structExplicitBinder` syntax node for a
    structure field: `(name : type)`. -/
private def mkFieldBinder
    (name : Lean.Ident) (type : Lean.Syntax)
    : Lean.Syntax :=
  Lean.Syntax.node .none
    ``Lean.Parser.Command.structExplicitBinder
    #[Lean.mkAtom "(",
      Lean.Syntax.node .none `null #[name],
      Lean.Syntax.node .none `null
        #[Lean.mkAtom ":", type],
      Lean.Syntax.node .none `null #[],
      Lean.Syntax.node .none `null #[],
      Lean.mkAtom ")"]

/-- Build a `structFields` node from an array of field binders. -/
private def mkStructFields
    (binders : Array Lean.Syntax) : Lean.Syntax :=
  Lean.Syntax.node .none ``Lean.Parser.Command.structFields
    #[Lean.Syntax.node .none `null binders]

/-- Extract field name, type, and doc from a `structField`
    syntax node. -/
private def parseStructField
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM
        (Lean.Ident × Lean.Syntax × Lean.TSyntax `str) := do
  match stx with
  | `(structField| | $n:ident $d:str : $t:term) =>
    pure (n, t, d)
  | _ => Lean.Elab.throwUnsupportedSyntax

open Lean Elab Command in
elab_rules : command
  | `(defStruct $name:ident ($symDoc:term) $doc:str where
       $fs:structField* $[deriving $derivs:ident,*]?) => do
    let fieldData ← fs.mapM parseStructField
    let binders ← fieldData.mapM fun (fn, ft, _) =>
      pure (mkFieldBinder fn ft)
    let fields := mkStructFields binders
    let structBody :=
      Lean.Syntax.node .none
        ``Lean.Parser.Command.structCtor
        #[mkNullNode', mkNullNode']
    let inductiveCmd :=
      Lean.Syntax.node .none
        ``Lean.Parser.Command.declaration
        #[mkEmptyDeclModifiers,
          Lean.Syntax.node .none
            ``Lean.Parser.Command.structure
            #[Lean.mkAtom "structure",
              Lean.Syntax.node .none
                ``Lean.Parser.Command.declId
                #[name, mkNullNode'],
              mkNullNode',
              mkNullNode',
              Lean.Syntax.node .none `null
                #[Lean.mkAtom "where"],
              Lean.Syntax.node .none `null
                #[structBody],
              fields,
              mkNullNode',
              Lean.Syntax.node .none `null #[]]]
    elabCommand inductiveCmd
    let deriveNames : Array Ident := match derivs with
      | some ds => ds
      | none => #[mkIdent `DecidableEq, mkIdent `Repr]
    for d in deriveNames do
      let deriveCmd ← `(command|
        deriving instance $d:ident for $name)
      elabCommand deriveCmd
    let fieldDefs ← fieldData.mapM fun (fn, ft, fd) => do
      let ns : TSyntax `term :=
        quote (toString fn.getId)
      let typeStr :=
        if ft.isIdent
        then toString ft.getId
        else ft.reprint.getD (toString ft)
      let tn : TSyntax `term := quote typeStr
      `({ name := $ns, typeName := $tn,
          doc := $fd : FieldDef })
    let ns : TSyntax `term := quote (toString name.getId)
    let fieldList ← `([$[$fieldDefs],*])
    let structDefVal ← `(term|
      { name := $ns,
        symbolDoc := ($symDoc : Doc), doc := $doc,
        fields := $fieldList : StructDef })
    let defName := mkIdent (name.getId ++ `structDef)
    let defCmd ← `(command|
      def $defName : StructDef := $structDefVal)
    elabCommand defCmd
    let mod ← getMainModule
    let modName : TSyntax `term := quote mod
    let initCmd ← `(command|
      initialize registerStructDef $defName $modName)
    elabCommand initCmd
