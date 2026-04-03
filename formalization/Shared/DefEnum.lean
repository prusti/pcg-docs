import Shared.EnumDef
import Lean

open Lean in

declare_syntax_cat enumVariant

/-- A variant in a `defEnum` declaration: `| name "doc" "latex"`. -/
syntax "| " ident str str : enumVariant

/-- Define an enum type with cross-language export metadata.

    Generates:
    1. A Lean `inductive` type with `DecidableEq` and `Repr`
    2. A `.enumDef : EnumDef` for Rust/LaTeX export

    Example:
    ```
    defEnum Capability "A capability describes..." where
      | exclusive "Can be read, written, or mutably borrowed." "E"
      | read      "Can be read from."                          "R"
    ```
    produces `inductive Capability` and `Capability.enumDef`. -/
syntax "defEnum " ident str " where" enumVariant* : command

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
  | `(defEnum $name:ident $doc:str where $vs:enumVariant*) => do
    let varData ← vs.mapM fun v => match v with
      | `(enumVariant| | $vn:ident $vd:str $vl:str) =>
        pure (vn, vd, vl)
      | _ => throwError "invalid enum variant"
    let varNames := varData.map fun (vn, _, _) => vn
    let ctors := varNames.map mkCtorSyntax
    let inductiveCmd ← `(command|
      inductive $name where $[$ctors]*
        deriving DecidableEq, Repr)
    elabCommand inductiveCmd
    let varDefs ← varData.mapM fun (vn, vd, vl) => do
      let ns : TSyntax `term := quote (toString vn.getId)
      `({ name := $ns, doc := $vd, latex := $vl : VariantDef })
    let ns : TSyntax `term := quote (toString name.getId)
    let varList ← `([$[$varDefs],*])
    let enumDefVal ← `(term|
      { name := $ns, doc := $doc, variants := $varList
        : EnumDef })
    let defName := mkIdent (name.getId ++ `enumDef)
    let defCmd ← `(command|
      def $defName : EnumDef := $enumDefVal)
    elabCommand defCmd
