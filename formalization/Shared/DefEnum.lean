import Shared.Registry
import Lean

open Lean in

declare_syntax_cat enumVariantArg

/-- An argument in a `defEnum` variant: `(name : Type)`. -/
syntax "(" ident ":" term ")" : enumVariantArg

declare_syntax_cat enumVariant

/-- A variant in a `defEnum` declaration:
    `| name (arg : Ty)* "doc" (symbolDoc) (displayName)`. -/
syntax "| " ident enumVariantArg* str "(" term ")" "(" term ")"
    : enumVariant

/-- Define an enum type with cross-language export and presentation
    metadata.

    Generates:
    1. A Lean `inductive` type with the specified derived instances
       (defaults to `DecidableEq` and `Repr`)
    2. A `.enumDef : EnumDef` for export and document generation

    Variants may carry arguments:
    ```
    defEnum Region (.italic (.text "r"))
      "A region (lifetime) in the MIR."
    where
      | vid (v : RegionVid) "A region variable identifier."
          (.text "vid") (.text "vid")
      | static "The 'static lifetime."
          (.text "static") (.text "static")
    ```

    A custom `deriving` clause overrides the default:
    ```
    defEnum Ty (.italic (.text "τ")) "A MIR type."
    where
      | param (index : Nat) "..." (.text "param") (.text "param")
      deriving Repr
    ``` -/
syntax "defEnum " ident "(" term ")" str " where"
    enumVariant* ("deriving " ident,+)? : command

private def mkNullNode' : Lean.Syntax :=
  Lean.Syntax.node .none `null #[]

private def mkEmptyDeclModifiers : Lean.Syntax :=
  Lean.Syntax.node .none ``Lean.Parser.Command.declModifiers
    #[mkNullNode', mkNullNode', mkNullNode',
      mkNullNode', mkNullNode', mkNullNode', mkNullNode']

/-- Build an `explicitBinder` syntax node: `(name : type)`. -/
private def mkExplicitBinder
    (name : Lean.Ident) (type : Lean.Syntax) : Lean.Syntax :=
  Lean.Syntax.node .none ``Lean.Parser.Term.explicitBinder
    #[Lean.mkAtom "(",
      Lean.Syntax.node .none `null #[name],
      Lean.Syntax.node .none `null #[Lean.mkAtom ":", type],
      Lean.Syntax.node .none `null #[],
      Lean.mkAtom ")"]

/-- Build an `optDeclSig` syntax node from an array of binders. -/
private def mkOptDeclSig
    (binders : Array Lean.Syntax) : Lean.Syntax :=
  Lean.Syntax.node .none ``Lean.Parser.Command.optDeclSig
    #[Lean.Syntax.node .none `null binders,
      Lean.Syntax.node .none `null #[]]

/-- Build a `Lean.Parser.Command.ctor` syntax node for a
    constructor with the given name and binders. -/
private def mkCtorSyntax
    (vn : Lean.Ident)
    (binders : Array Lean.Syntax)
    : Lean.TSyntax ``Lean.Parser.Command.ctor :=
  ⟨Lean.Syntax.node .none ``Lean.Parser.Command.ctor
    #[mkNullNode',
      Lean.mkAtom "|",
      mkEmptyDeclModifiers,
      vn,
      mkOptDeclSig binders]⟩

/-- Extract the argument name and type term from an
    `enumVariantArg` syntax node. -/
private def parseVariantArg
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM
        (Lean.Ident × Lean.Syntax) := do
  match stx with
  | `(enumVariantArg| ($n:ident : $t:term)) =>
    pure (n, t)
  | _ => Lean.Elab.throwUnsupportedSyntax

open Lean Elab Command in
elab_rules : command
  | `(defEnum $name:ident ($symDoc:term) $doc:str where
       $vs:enumVariant* $[deriving $derivs:ident,*]?) => do
    let varData ← vs.mapM fun v => match v with
      | `(enumVariant|
            | $vn:ident $args:enumVariantArg*
              $vd:str ($vlDoc:term) ($dn:term)) =>
        pure (vn, args, vd, vlDoc, dn)
      | _ => throwError "invalid enum variant"
    let ctors ← varData.mapM fun (vn, args, _, _, _) => do
      let binders ← args.mapM fun a => do
        let (argName, argType) ← parseVariantArg a
        let prefixed := mkIdent
          (Name.mkSimple s!"_{argName.getId}")
        pure (mkExplicitBinder prefixed argType)
      pure (mkCtorSyntax vn binders)
    let inductiveCmd ← `(command|
      inductive $name where $[$ctors]*)
    elabCommand inductiveCmd
    let deriveNames : Array Ident := match derivs with
      | some ds => ds
      | none => #[mkIdent `DecidableEq, mkIdent `Repr]
    for d in deriveNames do
      let deriveCmd ← `(command|
        deriving instance $d:ident for $name)
      elabCommand deriveCmd
    let varDefs ←
      varData.mapM fun (vn, args, vd, vlDoc, dn) => do
        let ns : TSyntax `term := quote (toString vn.getId)
        let argDefs ← args.mapM fun a => do
          let (argName, argType) ← parseVariantArg a
          let an : TSyntax `term :=
            quote (toString argName.getId)
          let typeStr :=
            if argType.isIdent
            then toString argType.getId
            else argType.reprint.getD
              (toString argType)
          let tn : TSyntax `term := quote typeStr
          `({ name := $an, typeName := $tn : ArgDef })
        let argList ← `([$[$argDefs],*])
        `({ name := $ns, doc := $vd,
            symbolDoc := ($vlDoc : Doc),
            displayName := ($dn : Doc),
            args := $argList
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
    let mod ← getMainModule
    let modName : TSyntax `term := quote mod
    let initCmd ← `(command|
      initialize registerEnumDef $defName $modName)
    elabCommand initCmd
