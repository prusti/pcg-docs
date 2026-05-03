import Core.Doc.Interp
import Core.Registry
import Core.Dsl.ElabUtils
import Core.Dsl.Lint
import Lean

open Core.Dsl.ElabUtils

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
    `| name (arg : Ty)* doc (displayExpr)?`.

    `doc` is any `Doc`-typed term (a string literal coerces
    to `Doc.plain`). The optional display expression is a
    single `MathDoc`-valued term — typically a `mathdoc!`
    literal — that may reference the variant's arguments by
    name. The `defEnum` elaborator wraps the expression in a
    function over the variant's args, so a free identifier
    `idx` inside the expression resolves to the bound
    `idx : MathDoc` parameter at rendering time. When
    omitted, the display defaults to the constructor name
    followed by each argument's symbol separated by spaces. -/
syntax "| " ident enumVariantArg* term:max
    ("(" term ")")? : enumVariant

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
    `structDef`. Retained for use by `defStruct` /
    `defFn` / `defProperty`, whose display templates are
    still `List DisplayPart`. The `defEnum` flow uses
    `buildArgSymbolDoc` (below) instead, since variant
    displays are now `MathDoc`-valued functions. -/
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
    let head := (tn.splitOn " ").headD tn
    let tnName := Name.mkSimple head
    let ns : TSyntax `term := quote argName
    if head == selfName then
      `(DisplayPart.arg $ns ($selfSym : MathDoc))
    else if typeParams.contains head then
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
      let raw : TSyntax `term := quote argName
      `(DisplayPart.arg $ns (MathDoc.text $raw))
    else
      throwError
        s!"defEnum: no enumDef, structDef, or aliasDef \
           found for type '{tn}'"

open Lean Elab Command in
/-- Parse a `displayPart` into a quoted `DisplayPart` term.
    Used by `defStruct` / `defFn` / `defProperty`. `argTypes`
    maps argument names to Lean type names for auto-lookup
    of `symbolDoc`; `selfName` / `selfSym` cover self-
    referential types; `typeParams` is the list of type-
    parameter names whose argument slots render as a plain
    math symbol. -/
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
/-- Build the `MathDoc` symbol for a variant argument: the
    auto-looked-up `symbolDoc` of the argument's declared
    type. `argTypes` maps argument names to their Lean type
    names. `selfName` / `selfSym` cover the self-referential
    case (an arg whose type is the enum itself). `typeParams`
    lists the enum-level type-parameter names; arguments of
    those types render using the parameter name as a plain
    math symbol. Returns the `MathDoc` term (an alternative
    fallback for primitive containers / unregistered types
    is `MathDoc.text "<argName>"`). -/
def buildArgSymbolDoc
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
    if head == selfName then
      `(($selfSym : MathDoc))
    else if typeParams.contains head then
      -- Type-parameter-typed argument: render using
      -- the parameter name as a plain math symbol.
      let raw : TSyntax `term := quote head
      `(MathDoc.text $raw)
    else if env.find? (tnName ++ `enumDef)
        |>.isSome then
      let ref := mkIdent
        (tnName ++ `enumDef ++ `symbolDoc)
      `($ref)
    else if env.find? (tnName ++ `structDef)
        |>.isSome then
      let ref := mkIdent
        (tnName ++ `structDef ++ `symbolDoc)
      `($ref)
    else if env.find? (tnName ++ `aliasDef)
        |>.isSome then
      let ref := mkIdent
        (tnName ++ `aliasDef ++ `symbolDoc)
      `($ref)
    else if ["Set", "List", "Option", "Map", "Nat",
             "Bool", "Int", "String",
             "UInt8", "UInt16", "UInt32", "UInt64",
             "USize"].contains head then
      -- DSL primitive container or scalar (`Set P`, `List X`,
      -- `Option Y`, `Map K V`, `Nat`, …): no registered
      -- `symbolDoc` exists, so fall back to rendering the
      -- argument by its name in the variant's default
      -- display template.
      let raw : TSyntax `term := quote argName
      `(MathDoc.text $raw)
    else
      throwError
        s!"defEnum: no enumDef, structDef, or aliasDef \
           found for type '{tn}'"

/-- Whether a free identifier reference to `name` appears
    anywhere inside `stx`. Used by `buildVariantDisplayFn` to
    skip pattern-bindings for variant arguments that the
    user-written display expression never references — keeps
    the generated `display` function clear of
    unused-variable linter warnings. -/
private partial def hasIdentRef (stx : Lean.Syntax)
    (name : Lean.Name) : Bool :=
  if stx.isIdent && stx.getId == name then true
  else stx.getArgs.any (hasIdentRef · name)

open Lean Elab Command in
/-- Wrap a user-written `MathDoc` display expression in a
    function over the variant's arguments. The generated
    function takes a positional `List MathDoc` and pattern-
    matches on its length: when the list shape matches the
    variant's arity, each entry binds the corresponding
    argument and the user expression is evaluated; otherwise
    the function returns `MathDoc.raw ""`.

    Pattern bindings use a `__display` suffix on each
    argument name to avoid clashing with same-named
    constructors of the enum being defined (e.g. an `arg ptr
    : ThinPointer` on a `Value.ptr` variant — both are named
    `ptr` and a bare `ptr` pattern would resolve to the
    constructor). Each suffixed binding is then `let`-bound
    to the user-visible argument name so the user expression
    can reference it directly. Argument names that the user
    expression never references are pattern-bound to `_`
    (and skip the `let`) so the generated function does not
    trip Lean's unused-variable linter.

    Accepting a `List MathDoc` (rather than a curried
    `MathDoc → … → MathDoc`) lets `VariantDef.display` have
    a uniform type across variants of differing arity, so
    `EnumDef` can store the function in a single field. -/
private def buildVariantDisplayFn
    (argIdents : Array Lean.Ident)
    (userTerm : Lean.TSyntax `term)
    : Lean.Elab.Command.CommandElabM
        (Lean.TSyntax `term) := do
  let wildcard : TSyntax `term ← `(_)
  let suffix (i : Lean.Ident) : Lean.Ident :=
    Lean.mkIdent (Lean.Name.mkSimple s!"{i.getId}__display")
  let patTerms : TSyntaxArray `term ←
    argIdents.mapM fun i => do
      if hasIdentRef userTerm.raw i.getId then
        pure (⟨(suffix i).raw⟩ : TSyntax `term)
      else
        pure wildcard
  -- Build the let-chain: for each user-visible arg name
  -- referenced in the user expression, bind it to the
  -- pattern-suffixed name so `idx` in the user expression
  -- resolves to the matched value.
  let mut body := userTerm
  for i in argIdents do
    if hasIdentRef userTerm.raw i.getId then
      let suff := suffix i
      body ← `(let $i:ident : MathDoc := $suff:ident; $body)
  `(fun (variantArgs__ : List MathDoc) =>
      match variantArgs__ with
      | [$patTerms,*] => ($body : MathDoc)
      | _ => MathDoc.raw "")

open Lean Elab Command in
/-- Build the default variant display: the constructor name
    followed by each argument's bound `MathDoc` reference
    separated by `MathSym.space`. Returns a complete
    `List MathDoc → MathDoc` function suitable for storing
    directly in `VariantDef.display`. -/
private def buildDefaultVariantDisplay
    (ctorName : String)
    (argIdents : Array Lean.Ident)
    : Lean.Elab.Command.CommandElabM
        (Lean.TSyntax `term) := do
  let ctorStr : TSyntax `term := quote ctorName
  let mut parts : Array (TSyntax `term) :=
    #[← `(MathDoc.text $ctorStr)]
  for ai in argIdents do
    parts := parts.push (← `(MathDoc.sym MathSym.space))
    parts := parts.push (← `(($ai:ident : MathDoc)))
  let userTerm ← `(MathDoc.seq [$parts,*])
  buildVariantDisplayFn argIdents userTerm

/-- The Lean-source rendering of every `($n : T)` argument's
    type across all `varData` entries. Used by
    `variantArgsUseHash` (and nowhere else) to feed the type
    strings to `usesHashPropagating`. -/
private def variantArgTypeStrs
    (varData : Array
      (Lean.TSyntax `ident × Array (Lean.TSyntax `enumVariantArg)
        × Lean.TSyntax `term × Option (Lean.TSyntax `term)))
    : List String :=
  varData.toList.flatMap fun (_, args, _, _) =>
    args.toList.filterMap fun (a : Lean.TSyntax _) =>
      match a.raw with
      | `(enumVariantArg| ($_:ident : $t:term)) =>
        some (toTypeStr t.raw)
      | _ => none

/-- Whether any variant argument's type drags `BEq`/`Hashable`
    constraints onto the enum's type parameters. Wraps
    `usesHashPropagating` for the `defEnum`-specific shape. -/
private def variantArgsUseHash
    (varData : Array
      (Lean.TSyntax `ident × Array (Lean.TSyntax `enumVariantArg)
        × Lean.TSyntax `term × Option (Lean.TSyntax `term)))
    : IO Bool :=
  usesHashPropagating (variantArgTypeStrs varData)

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
              $vd:term $[( $disp:term )]?) =>
        pure (vn, args, vd, disp)
      | _ => throwError "invalid enum variant"
    let typeParamNames : List String := typeParamNames tps
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
      let argsUseHash ← variantArgsUseHash varData
      let tpBinders ←
        mkTypeParamBinders typeParamNames argsUseHash
      let derivIds : Array Ident := match derivs with
        | some ds => ds.getElems
        | none => defaultDerives
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
        | none => defaultDerives
      for d in deriveNames do
        let deriveCmd ← `(command|
          deriving instance $d:ident for $name)
        elabCommand deriveCmd
    let varDefs ←
      varData.mapM fun (vn, args, vd, disp) => do
        let vnStr : TSyntax `term :=
          quote (toString vn.getId)
        let ns ← `(DSLIdent.mk $vnStr)
        let argTypes ← args.toList.mapM
          fun (a : Lean.TSyntax `enumVariantArg) => do
          let (an, at_) ← parseVariantArg a.raw
          pure (toString an.getId, toTypeStr at_)
        let selfN := toString name.getId
        -- Per-arg `Ident`s used both as the binders in the
        -- variant's display function and as the argument-
        -- name strings stored in `ArgDef`. Computing the
        -- list once keeps the two outputs in lock-step.
        let argIdents ← args.mapM fun a => do
          let (argName, _) ← parseVariantArg a
          pure argName
        let argDefs ← args.mapM fun a => do
          let (argName, argType) ← parseVariantArg a
          let an : TSyntax `term :=
            quote (toString argName.getId)
          let tn : TSyntax `term := quote (toTypeStr argType)
          let symDocTerm ← buildArgSymbolDoc
            (toString argName.getId) argTypes selfN
            symDoc typeParamNames
          `({ name := $an,
              type := DSLType.parse $tn,
              symbolDoc := $symDocTerm
              : ArgDef })
        let argList ← `([$[$argDefs],*])
        let displayFn ← match disp with
          | some t => buildVariantDisplayFn argIdents t
          | none =>
            buildDefaultVariantDisplay
              (toString vn.getId) argIdents
        `({ name := $ns, doc := ($vd : Doc),
            display := $displayFn,
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
    registerInCurrentModule ``registerEnumDef defName
    -- A generic enum that uses `Map`/`Set` (directly or
    -- transitively, via a previously-registered hash-
    -- propagating type) propagates `BEq`/`Hashable`
    -- constraints to its type parameters; record this so
    -- downstream `defStruct` / `defEnum` declarations
    -- referencing this enum drag in the same constraints.
    -- Recorded via an `initialize` block so the registration
    -- survives across module loads.
    if isGeneric then
      let argsUseHash ← variantArgsUseHash varData
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
    DslLint.lintDocTerm doc
    elabDefEnum name tps symDoc setDoc defnName doc
      false false vs derivs
  | `(defEnum $name:ident $[{ $tps:ident* }]?
       ($symDoc:term, $setDoc:term)
       $defnName:str ($doc:term) long where
       $vs:enumVariant* $[deriving $derivs:ident,*]?) => do
    DslLint.lintDocTerm doc
    elabDefEnum name tps symDoc setDoc defnName doc
      true false vs derivs
  | `(defEnum $name:ident $[{ $tps:ident* }]?
       ($symDoc:term, $setDoc:term)
       $defnName:str ($doc:term) subscript where
       $vs:enumVariant* $[deriving $derivs:ident,*]?) => do
    DslLint.lintDocTerm doc
    elabDefEnum name tps symDoc setDoc defnName doc
      false true vs derivs
  | `(defEnum $name:ident $[{ $tps:ident* }]?
       ($symDoc:term, $setDoc:term)
       $defnName:str ($doc:term) long subscript where
       $vs:enumVariant* $[deriving $derivs:ident,*]?) => do
    DslLint.lintDocTerm doc
    elabDefEnum name tps symDoc setDoc defnName doc
      true true vs derivs
