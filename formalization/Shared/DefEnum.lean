import Shared.EnumDef
import Lean

open Lean in

declare_syntax_cat enumVariant

/-- A variant in a `defEnum` declaration:
    `| name "doc" (symbolDoc) (displayName)`. -/
syntax "| " ident str "(" term ")" "(" term ")" : enumVariant

/-- Define an enum type with cross-language export and presentation
    metadata.

    Generates:
    1. A Lean `inductive` type with `DecidableEq` and `Repr`
    2. A `.enumDef : EnumDef` for export and document generation

    Example:
    ```
    defEnum Capability (.italic (.text "c"))
      "A capability describes..."
    where
      | exclusive "Can be read, written, or mutably borrowed."
          (.bold (.text "E"))
          (.seq [.bold (.text "E"), .text "xclusive"])
      | read "Can be read from."
          (.bold (.text "R"))
          (.seq [.bold (.text "R"), .text "ead"])
    ```
    produces `inductive Capability` and `Capability.enumDef`. -/
syntax "defEnum " ident "(" term ")" str " where"
    enumVariant* : command

private def mkNullNode' : Lean.Syntax :=
  Lean.Syntax.node .none `null #[]

private def mkEmptyDeclModifiers : Lean.Syntax :=
  Lean.Syntax.node .none ``Lean.Parser.Command.declModifiers
    #[mkNullNode', mkNullNode', mkNullNode',
      mkNullNode', mkNullNode', mkNullNode', mkNullNode']

private def mkEmptyOptDeclSig : Lean.Syntax :=
  Lean.Syntax.node .none ``Lean.Parser.Command.optDeclSig
    #[mkNullNode', mkNullNode']

/-- Build a `Lean.Parser.Command.ctor` syntax node for a
    nullary constructor with the given name. -/
private def mkCtorSyntax
    (vn : Lean.Ident)
    : Lean.TSyntax ``Lean.Parser.Command.ctor :=
  ⟨Lean.Syntax.node .none ``Lean.Parser.Command.ctor
    #[mkNullNode',
      Lean.mkAtom "|",
      mkEmptyDeclModifiers,
      vn,
      mkEmptyOptDeclSig]⟩

open Lean Elab Command in
elab_rules : command
  | `(defEnum $name:ident ($symDoc:term) $doc:str where
       $vs:enumVariant*) => do
    let varData ← vs.mapM fun v => match v with
      | `(enumVariant|
            | $vn:ident $vd:str ($vlDoc:term)
              ($dn:term)) =>
        pure (vn, vd, vlDoc, dn)
      | _ => throwError "invalid enum variant"
    let varNames := varData.map fun (vn, _, _, _) => vn
    let ctors := varNames.map mkCtorSyntax
    let inductiveCmd ← `(command|
      inductive $name where $[$ctors]*
        deriving DecidableEq, Repr)
    elabCommand inductiveCmd
    let varDefs ←
      varData.mapM fun (vn, vd, vlDoc, dn) => do
        let ns : TSyntax `term := quote (toString vn.getId)
        `({ name := $ns, doc := $vd,
            symbolDoc := ($vlDoc : Doc),
            displayName := ($dn : Doc)
            : VariantDef })
    let ns : TSyntax `term := quote (toString name.getId)
    let varList ← `([$[$varDefs],*])
    let enumDefVal ← `(term|
      { name := $ns,
        symbolDoc := ($symDoc : Doc), doc := $doc,
        variants := $varList : EnumDef })
    let defName := mkIdent (name.getId ++ `enumDef)
    let defCmd ← `(command|
      def $defName : EnumDef := $enumDefVal)
    elabCommand defCmd
