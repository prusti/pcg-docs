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
    `| name (arg : Ty)* doc (displayPart, ...)`.

    `doc` is any `Doc`-typed term (a string literal coerces
    to `Doc.plain`). The display template is optional. If
    omitted, it defaults to the constructor name followed by
    each argument's symbol separated by spaces. -/
syntax "| " ident enumVariantArg* term:max
    ("(" displayPart,+ ")")? : enumVariant

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
          (.text "vid", .sym .lparen, #v, .sym .rparen)
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
          (.text "param ", #index (.raw "i"))
      deriving Repr
    ``` -/
syntax "defEnum " ident ("{" ident+ "}")?
    "(" term "," term ")" str "(" term ")"
    ("long")? ("subscript")?
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
/-- Build a `DisplayPart.arg` term for an argument whose
    symbol is auto-looked-up from its type's `enumDef`/
    `structDef`. See `parseDisplayPart` for argument
    descriptions. -/
def buildArgRef
    (argName : String)
    (argTypes : List (String × String))
    (selfName : String)
    (selfSym : Lean.TSyntax `term)
    (typeParams : List String)
    : Lean.Elab.Command.CommandElabM
        (Lean.TSyntax `term) := do
  let typeName := argTypes.find?
    (·.1 == argName) |>.map (·.2)
  match typeName with
  | none =>
    throwError
      s!"defEnum: unknown argument '{argName}'"
  | some tn =>
    let env ← getEnv
    -- For generic-application types like
    -- `"LifetimeProjection (PcgPlace P) Nat"`, look up
    -- the head identifier (first whitespace-separated
    -- token) rather than the full applied form.
    let head := (tn.splitOn " ").headD tn
    let tnName := Name.mkSimple head
    let ns : TSyntax `term := quote argName
    if head == selfName then
      `(DisplayPart.arg $ns ($selfSym : MathDoc))
    else if typeParams.contains head then
      -- Type-parameter-typed argument: render using
      -- the parameter name as a plain math symbol.
      let raw : TSyntax `term := quote head
      `(DisplayPart.arg $ns (MathDoc.text $raw))
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
    else if env.find? (tnName ++ `aliasDef)
        |>.isSome then
      let ref := mkIdent
        (tnName ++ `aliasDef ++ `symbolDoc)
      `(DisplayPart.arg $ns $ref)
    else if ["Set", "List", "Option", "Map", "Nat",
             "Bool", "Int", "String"].contains head then
      -- DSL primitive container or scalar (`Set P`, `List X`,
      -- `Option Y`, `Map K V`, `Nat`, …): no registered
      -- `symbolDoc` exists, so fall back to rendering the
      -- argument by its name in the variant's default
      -- display template.
      let raw : TSyntax `term := quote argName
      `(DisplayPart.arg $ns (MathDoc.text $raw))
    else
      throwError
        s!"defEnum: no enumDef, structDef, or aliasDef \
           found for type '{tn}'"

open Lean Elab Command in
/-- Parse a `displayPart` into a quoted `DisplayPart` term.
    `argTypes` maps argument names to their Lean type names
    for auto-lookup of symbolDoc. `selfName` is the enum
    being defined (for self-referential types). `selfSym`
    is the self-type's symbolDoc syntax. `typeParams` is
    the list of enum-level type parameter names; arguments
    of those types render using the parameter name as a
    plain symbol. -/
def parseDisplayPart
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
  | `(displayPart| # $n:ident) =>
    buildArgRef (toString n.getId) argTypes
      selfName selfSym typeParams
  | `(displayPart| $t:term) =>
    `(DisplayPart.lit ($t : MathDoc))
  | _ => Lean.Elab.throwUnsupportedSyntax

open Lean Elab Command in
/-- Build the default display template for a variant when
    no explicit one is given: the plain constructor name,
    followed by each argument's auto-looked-up symbol
    separated by spaces. -/
private def defaultDisplayParts
    (ctorName : String)
    (args : Array (Lean.TSyntax `enumVariantArg))
    (argTypes : List (String × String))
    (selfName : String)
    (selfSym : Lean.TSyntax `term)
    (typeParams : List String)
    : Lean.Elab.Command.CommandElabM
        (Array (Lean.TSyntax `term)) := do
  let ctorStr : TSyntax `term := quote ctorName
  let ctorPart ← `(DisplayPart.lit (MathDoc.text $ctorStr))
  let mut parts : Array (Lean.TSyntax `term) := #[ctorPart]
  for a in args do
    let (argName, _) ← parseVariantArg a.raw
    let spacePart ← `(DisplayPart.lit
        (MathDoc.sym MathSym.space))
    let argRef ← buildArgRef
      (toString argName.getId) argTypes
      selfName selfSym typeParams
    parts := parts ++ #[spacePart, argRef]
  pure parts

open Lean Elab Command in
/-- Shared elaboration body for the `defEnum` forms.
    `longDefVal` controls the formal LaTeX rendering (short
    `::=` vs. long `where`-style form). `subscriptDefVal`
    controls whether the type symbol gets a subscript of its
    type parameters in the LaTeX presentation. -/
private def elabDefEnum
    (name : TSyntax `ident)
    (tps : Option (TSyntaxArray `ident))
    (symDoc setDoc : TSyntax `term)
    (defnName : TSyntax `str)
    (doc : TSyntax `term)
    (longDefVal : Bool)
    (subscriptDefVal : Bool)
    (vs : TSyntaxArray `enumVariant)
    (derivs : Option (Syntax.TSepArray `ident ","))
    : CommandElabM Unit := do
    let varData ← vs.mapM fun v => match v with
      | `(enumVariant|
            | $vn:ident $args:enumVariantArg*
              $vd:term $[( $dps:displayPart,* )]?) =>
        pure (vn, args, vd, dps)
      | _ => throwError "invalid enum variant"
    let typeParamNames : List String := match tps with
      | some ids => ids.toList.map (toString ·.getId)
      | none => []
    let isGeneric := !typeParamNames.isEmpty
    -- Build ctors using the user's original `argType`
    -- syntax so identifier source positions survive and
    -- editor features like go-to-definition work on type
    -- references inside variant arguments.
    let ctors ← varData.mapM
      fun (vn, args, _, _) => do
        let binders ← args.mapM fun a => do
          let (argName, argType) ← parseVariantArg a
          let prefixed := mkIdent
            (Name.mkSimple s!"_{argName.getId}")
          pure (mkExplicitBinder prefixed argType)
        pure (mkCtorSyntax vn binders)
    if isGeneric then
      -- Generic inductives embed `deriving` in the
      -- declaration and take `(P : Type)` binders for
      -- each parameter. When a variant argument uses `Map`
      -- or `Set` (which expand to `Std.HashMap`/
      -- `Std.HashSet`, whose element type requires `BEq` and
      -- `Hashable`), append `[BEq P] [Hashable P]` instance
      -- binders so the generated inductive type-checks under
      -- `autoImplicit := false` — mirroring `defStruct`.
      let propagating ← hashPropagatingTypes.get
      let argsUseHash := varData.any fun (_, args, _, _) =>
        args.any fun a => match a with
          | `(enumVariantArg| ($_:ident : $t:term)) =>
            let typeStr :=
              if t.raw.isIdent then toString t.raw.getId
              else t.raw.reprint.getD (toString t)
            let chars := typeStr.toList.map fun c =>
              if c == '(' || c == ')' then ' ' else c
            let tokens : List String :=
              String.ofList chars
                |>.splitOn " "
                |>.filter (· != "")
            tokens.any fun tok =>
              tok == "Map" || tok == "Set" ||
                propagating.contains tok
          | _ => false
      let tpBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)
        ← typeParamNames.toArray.foldlM
            (init := #[]) fun acc p => do
              let pId := mkIdent (Name.mkSimple p)
              let typeBinder ← `(Lean.Parser.Term.bracketedBinderF|
                ($pId : Type))
              if argsUseHash then
                let beq ← `(Lean.Parser.Term.bracketedBinderF|
                  [BEq $pId])
                let hash ← `(Lean.Parser.Term.bracketedBinderF|
                  [Hashable $pId])
                pure (acc.push typeBinder |>.push beq
                          |>.push hash)
              else
                pure (acc.push typeBinder)
      let derivIds : Array Ident := match derivs with
        | some ds => ds.getElems
        | none => #[mkIdent `DecidableEq,
                    mkIdent `Repr, mkIdent `Hashable]
      let inductiveCmd ← `(command|
        inductive $name:ident $tpBinders:bracketedBinder*
          where
        $[$ctors:ctor]*
        deriving $[$derivIds:ident],*)
      elabCommand inductiveCmd
    else
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
        let ns ← `(DSLIdent.mk $vnStr)
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
        let dpDefs ← match dps with
          | some dps =>
            dps.getElems.mapM
              (parseDisplayPart argTypes selfN symDoc
                typeParamNames)
          | none =>
            defaultDisplayParts (toString vn.getId) args
              argTypes selfN symDoc typeParamNames
        let dpList ← `([$[$dpDefs],*])
        `({ name := $ns, doc := ($vd : Doc),
            display := $dpList,
            args := $argList
            : VariantDef })
    let enumNameStr : TSyntax `term :=
      quote (toString name.getId)
    let ns ← `(DSLIdent.mk $enumNameStr)
    let varList ← `([$[$varDefs],*])
    let typeParamsTerm : TSyntax `term :=
      quote typeParamNames
    let longFormTerm : TSyntax `term ←
      if longDefVal then `(true) else `(false)
    let subscriptTerm : TSyntax `term ←
      if subscriptDefVal then `(true) else `(false)
    -- Expose `symDoc`, `setDoc`, and `typeParams` as
    -- unhygienic identifiers so user-written doc terms
    -- (and the `defMathSelf` macro) can reference them.
    let symDocId := mkIdent `symDoc
    let setDocId := mkIdent `setDoc
    let typeParamsId := mkIdent `typeParams
    let enumDefVal ← `(term|
      { name := $ns,
        symbolDoc := ($symDoc : MathDoc),
        setDoc := ($setDoc : MathDoc),
        defnName := $defnName,
        doc := (
          let $symDocId : MathDoc := ($symDoc : MathDoc);
          let $setDocId : MathDoc := ($setDoc : MathDoc);
          let $typeParamsId : List String := $typeParamsTerm;
          ($doc : Doc)),
        typeParams := $typeParamsTerm,
        useLongForm := $longFormTerm,
        subscriptTypeParams := $subscriptTerm,
        variants := $varList : EnumDef })
    let defName := mkIdent (name.getId ++ `enumDef)
    elabCommand (← `(command|
      def $defName : EnumDef := $enumDefVal))
    let mod ← getMainModule
    let modName : TSyntax `term := quote mod
    elabCommand (← `(command|
      initialize registerEnumDef $defName $modName))
    -- A generic enum that uses `Map`/`Set` (directly or
    -- transitively, via a previously-registered hash-
    -- propagating type) propagates `BEq`/`Hashable`
    -- constraints to its type parameters; record this so
    -- downstream `defStruct` / `defEnum` declarations
    -- referencing this enum drag in the same constraints.
    -- Recorded via an `initialize` block so the registration
    -- survives across module loads.
    if isGeneric then
      let propagating ← hashPropagatingTypes.get
      let argsUseHash := varData.any fun (_, args, _, _) =>
        args.any fun a => match a with
          | `(enumVariantArg| ($_:ident : $t:term)) =>
            let typeStr :=
              if t.raw.isIdent then toString t.raw.getId
              else t.raw.reprint.getD (toString t)
            let chars := typeStr.toList.map fun c =>
              if c == '(' || c == ')' then ' ' else c
            let tokens : List String :=
              String.ofList chars
                |>.splitOn " "
                |>.filter (· != "")
            tokens.any fun tok =>
              tok == "Map" || tok == "Set" ||
                propagating.contains tok
          | _ => false
      if argsUseHash then
        let nameTerm : TSyntax `term :=
          quote (toString name.getId)
        elabCommand (← `(command|
          initialize registerHashPropagating $nameTerm))

open Lean Elab Command in
elab_rules : command
  | `(defEnum $name:ident $[{ $tps:ident* }]?
       ($symDoc:term, $setDoc:term)
       $defnName:str ($doc:term) where
       $vs:enumVariant* $[deriving $derivs:ident,*]?) => do
    elabDefEnum name tps symDoc setDoc defnName doc
      false false vs derivs
  | `(defEnum $name:ident $[{ $tps:ident* }]?
       ($symDoc:term, $setDoc:term)
       $defnName:str ($doc:term) long where
       $vs:enumVariant* $[deriving $derivs:ident,*]?) => do
    elabDefEnum name tps symDoc setDoc defnName doc
      true false vs derivs
  | `(defEnum $name:ident $[{ $tps:ident* }]?
       ($symDoc:term, $setDoc:term)
       $defnName:str ($doc:term) subscript where
       $vs:enumVariant* $[deriving $derivs:ident,*]?) => do
    elabDefEnum name tps symDoc setDoc defnName doc
      false true vs derivs
  | `(defEnum $name:ident $[{ $tps:ident* }]?
       ($symDoc:term, $setDoc:term)
       $defnName:str ($doc:term) long subscript where
       $vs:enumVariant* $[deriving $derivs:ident,*]?) => do
    elabDefEnum name tps symDoc setDoc defnName doc
      true true vs derivs
