import Core.Registry
import Lean

open Lean in

declare_syntax_cat enumVariantArg

/-- An argument in a `defEnum` variant: `(name : Type)`. -/
syntax "(" ident ":" term ")" : enumVariantArg

declare_syntax_cat displayPart

/-- A literal `Doc` fragment in a display template. -/
syntax term : displayPart

/-- An argument reference with its display symbol:
    `#argName (symbolDoc)`. -/
syntax "#" ident "(" term ")" : displayPart

/-- An argument reference with auto-looked-up symbol from
    the argument type's `enumDef` or `structDef`. -/
syntax "#" ident : displayPart

declare_syntax_cat enumVariant

/-- A variant in a `defEnum` declaration:
    `| name (arg : Ty)* "doc" (displayPart, ...)`. -/
syntax "| " ident enumVariantArg* str
    "(" displayPart,+ ")" : enumVariant

/-- Define an enum type with cross-language export and presentation
    metadata.

    Generates:
    1. A Lean `inductive` type with the specified derived instances
       (defaults to `DecidableEq` and `Repr`)
    2. A `.enumDef : EnumDef` for export and document generation

    The long-form description is a `Doc` term, allowing rich
    content (inline code, links, math) rather than a plain string.

    Variants may carry arguments. Display parts are `MathDoc`:
    ```
    defEnum Region (.raw "r", .raw "R")
      "Regions"
      (.plain "A region (lifetime) in the MIR.")
    where
      | vid (v : RegionVid) "A region variable identifier."
          (.doc (.plain "vid"), .sym .lparen, #v, .sym .rparen)
      | static "The 'static lifetime."
          (.doc (.code "'static"))
    ```

    A custom `deriving` clause overrides the default:
    ```
    defEnum Ty (.raw "τ", .raw "Ty")
      "Types"
      (.plain "A MIR type.")
    where
      | param (index : Nat) "..."
          (.doc (.plain "param "), #index (.raw "i"))
      deriving Repr
    ``` -/
syntax "defEnum " ident ("{" ident+ "}")?
    "(" term "," term ")" str "(" term ")"
    " where"
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
/-- Parse a `displayPart` into a quoted `DisplayPart` term.
    `argTypes` maps argument names to their Lean type names
    for auto-lookup of symbolDoc. `selfName` is the enum
    being defined (for self-referential types). `selfSym`
    is the self-type's symbolDoc syntax. `typeParams` is
    the list of enum-level type parameter names; arguments
    of those types render using the parameter name as a
    plain symbol. -/
private def parseDisplayPart
    (argTypes : List (String × String))
    (selfName : String)
    (selfSym : Lean.TSyntax `term)
    (typeParams : List String)
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM
        (Lean.TSyntax `term) := do
  match stx with
  | `(displayPart| # $n:ident ($sym:term)) =>
    let ns : Lean.TSyntax `term :=
      Lean.quote (toString n.getId)
    `(DisplayPart.arg $ns ($sym : MathDoc))
  | `(displayPart| # $n:ident) => do
    let argName := toString n.getId
    let typeName := argTypes.find?
      (·.1 == argName) |>.map (·.2)
    match typeName with
    | none =>
      throwError
        s!"defEnum: unknown argument '{argName}'"
    | some tn =>
      let env ← getEnv
      let tnName := Name.mkSimple tn
      let ns : TSyntax `term := quote argName
      if tn == selfName then
        `(DisplayPart.arg $ns ($selfSym : MathDoc))
      else if typeParams.contains tn then
        -- Type-parameter-typed argument: render using
        -- the parameter name as a plain math symbol.
        let raw : TSyntax `term := quote tn
        `(DisplayPart.arg $ns
            (MathDoc.doc (Doc.plain $raw)))
      else if env.find? (tnName ++ `enumDef)
          |>.isSome then
        let ref := mkIdent
          (tnName ++ `enumDef ++ `symbolDoc)
        `(DisplayPart.arg $ns $ref)
      else if env.find? (tnName ++ `structDef)
          |>.isSome then
        let ref := mkIdent
          (tnName ++ `structDef ++ `symbolDoc)
        `(DisplayPart.arg $ns $ref)
      else
        throwError
          s!"defEnum: no enumDef or structDef \
             found for type '{tn}'"
  | `(displayPart| $t:term) =>
    `(DisplayPart.lit ($t : MathDoc))
  | _ => Lean.Elab.throwUnsupportedSyntax

open Lean Elab Command in
elab_rules : command
  | `(defEnum $name:ident $[{ $tps:ident* }]?
       ($symDoc:term, $setDoc:term)
       $defnName:str ($doc:term) where
       $vs:enumVariant* $[deriving $derivs:ident,*]?) => do
    let varData ← vs.mapM fun v => match v with
      | `(enumVariant|
            | $vn:ident $args:enumVariantArg*
              $vd:str ($dps:displayPart,*)) =>
        pure (vn, args, vd, dps)
      | _ => throwError "invalid enum variant"
    let typeParamNames : List String := match tps with
      | some ids => ids.toList.map (toString ·.getId)
      | none => []
    let isGeneric := !typeParamNames.isEmpty
    -- For generic enums we build the inductive declaration as
    -- a string and parse it (mirroring `defStruct`), so that
    -- type parameters and inline `deriving` can be attached.
    if isGeneric then
      let tpStr := " " ++ " ".intercalate
        (typeParamNames.map fun p => s!"\{{p} : Type}")
      let ctorStrs ← varData.toList.mapM
        fun (vn, args, _, _) => do
          let argStrs ← args.toList.mapM
            fun (a : Lean.TSyntax `enumVariantArg) => do
              let (argName, argType) ← parseVariantArg a.raw
              let typeStr :=
                if argType.isIdent then toString argType.getId
                else argType.reprint.getD (toString argType)
              -- Prefix with `_` to suppress
              -- `unused variable` linter warnings
              -- (matches the non-generic path).
              pure s!"(_{argName.getId} : {typeStr})"
          let argPart := if argStrs.isEmpty then ""
            else " " ++ " ".intercalate argStrs
          pure s!"  | {vn.getId}{argPart}"
      let derivClause :=
        "\n  deriving DecidableEq, Repr, Hashable"
      let inductiveStr :=
        s!"inductive {name.getId}{tpStr} where\n\
           {"\n".intercalate ctorStrs}\
           {derivClause}"
      let env ← getEnv
      match Parser.runParserCategory env `command
        inductiveStr with
      | .ok stx => elabCommand stx
      | .error e =>
        throwError s!"defEnum: parse error: {e}\n\
          ---\n{inductiveStr}\n---"
    else
      let ctors ← varData.mapM
        fun (vn, args, _, _) => do
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
        | none => #[mkIdent `DecidableEq, mkIdent `Repr,
                     mkIdent `Hashable]
      for d in deriveNames do
        let deriveCmd ← `(command|
          deriving instance $d:ident for $name)
        elabCommand deriveCmd
    let varDefs ←
      varData.mapM fun (vn, args, vd, dps) => do
        let vnStr : TSyntax `term :=
          quote (toString vn.getId)
        let ns ← `(DSLNamedTy.mk $vnStr)
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
          `({ name := $an,
              type := DSLType.parse $tn : ArgDef })
        let argList ← `([$[$argDefs],*])
        let argTypes ← args.toList.mapM
          fun (a : Lean.TSyntax `enumVariantArg) => do
          let (an, at_) ← parseVariantArg a.raw
          let tn := if at_.isIdent
            then toString at_.getId
            else at_.reprint.getD (toString at_)
          pure (toString an.getId, tn)
        let selfN := toString name.getId
        let dpDefs ← dps.getElems.mapM
          (parseDisplayPart argTypes selfN symDoc
            typeParamNames)
        let dpList ← `([$[$dpDefs],*])
        `({ name := $ns, doc := $vd,
            display := $dpList,
            args := $argList
            : VariantDef })
    let enumNameStr : TSyntax `term :=
      quote (toString name.getId)
    let ns ← `(DSLNamedTy.mk $enumNameStr)
    let varList ← `([$[$varDefs],*])
    let typeParamsTerm : TSyntax `term :=
      quote typeParamNames
    let enumDefVal ← `(term|
      { name := $ns,
        symbolDoc := ($symDoc : MathDoc),
        setDoc := ($setDoc : MathDoc),
        defnName := $defnName,
        doc := ($doc : Doc),
        typeParams := $typeParamsTerm,
        variants := $varList : EnumDef })
    let defName := mkIdent (name.getId ++ `enumDef)
    elabCommand (← `(command|
      def $defName : EnumDef := $enumDefVal))
    let mod ← getMainModule
    let modName : TSyntax `term := quote mod
    elabCommand (← `(command|
      initialize registerEnumDef $defName $modName))
