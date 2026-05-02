import Core.Doc.Interp
import Core.Registry
import Core.Dsl.IdentRefs
import Core.Dsl.Lint
import Core.Dsl.DefFn
import Lean

open Core.Dsl.IdentRefs

/-- Define a type alias with cross-language export metadata.

    Generates:
    1. A Lean `abbrev` bound to the aliased type.
    2. An `AliasDef` registry entry for downstream export.

    Example:
    ```
    defAlias LocalLifetimeProjection {P}
        (.text "llp",
         .text "LocalLifetimeProjection")
      "Local Lifetime Projections"
      (.plain "A local lifetime projection is a lifetime \
       projection whose base is a maybe-labelled place and \
       whose index is a natural number.")
      := LifetimeProjection (MaybeLabelled P) Nat
    ``` -/
syntax "defAlias " ident ("{" ident+ "}")?
    "(" term "," term ")"
    str "(" term ")"
    ":=" term : command

/-- Define a value alias (a constant) with cross-language
    export metadata.

    Generates:
    1. A Lean `def Name : Type := Body` declaration (the type
       is inferred from `Body` by Lean's elaborator).
    2. An `AliasDef` registry entry for downstream export. The
       Rust export emits `pub const NAME: Type = Body;` rather
       than `pub type Name = Body;`.

    Example:
    ```
    defAlias RETURN = Place⟨Local⟨0⟩, []⟩
    ```

    The body is parsed as a DSL `fnExpr` so anonymous-constructor
    syntax (`Name⟨a, b, …⟩`) and list literals work the same way
    they do inside `defFn` bodies. -/
syntax "defAlias " ident " = " fnExpr : command

open Lean Elab Command in
elab_rules : command
  | `(defAlias $name:ident $[{ $tps:ident* }]?
       ($symDoc:term, $setDoc:term)
       $docParam:str ($doc:term) := $body:term)
    => do
    DslLint.lintDocTerm doc
    let typeParamNames : List String := match tps with
      | some ids => ids.toList.map (toString ·.getId)
      | none => []
    let tpStr :=
      if typeParamNames.isEmpty then ""
      else " " ++ " ".intercalate
        (typeParamNames.map fun p => s!"({p} : Type)")
    let bodyStr :=
      if body.raw.isIdent then toString body.raw.getId
      else body.raw.reprint.getD (toString body.raw)
    let abbrevStr :=
      s!"abbrev {name.getId}{tpStr} := {bodyStr}"
    let env ← getEnv
    match Parser.runParserCategory env `command abbrevStr with
    | .ok stx =>
      let stx := graftUserNameToken name.getId name.raw stx
      elabCommand stx
    | .error e =>
      throwError s!"defAlias: parse error: {e}\n\
        ---\n{abbrevStr}\n---"
    setUserDeclRanges name (← getRef)
    let ns : TSyntax `term :=
      quote (toString name.getId)
    let typeParamsTerm : TSyntax `term :=
      quote typeParamNames
    let bodyTyTerm ← `(DSLType.parse $(quote bodyStr))
    let adId := mkIdent (name.getId ++ `aliasDef)
    -- Expose `symDoc`, `setDoc`, and `typeParams` as
    -- unhygienic identifiers so user-written doc terms
    -- (and the `defMathSelf` macro) can reference them.
    let symDocId := mkIdent `symDoc
    let setDocId := mkIdent `setDoc
    let typeParamsId := mkIdent `typeParams
    elabCommand (← `(command|
      def $adId : AliasDef :=
        { name := $ns,
          symbolDoc := ($symDoc : MathDoc),
          setDoc := ($setDoc : MathDoc),
          docParam := $docParam,
          doc := (
            let $symDocId : MathDoc := ($symDoc : MathDoc);
            let $setDocId : MathDoc := ($setDoc : MathDoc);
            let $typeParamsId : List String := $typeParamsTerm;
            ($doc : Doc)),
          typeParams := $typeParamsTerm,
          aliased := $bodyTyTerm,
          value := none }))
    let mod ← getMainModule
    let modName : TSyntax `term := quote mod
    elabCommand (← `(command|
      initialize registerAliasDef $adId $modName))

open Lean Elab Command Core.Dsl.IdentRefs in
elab_rules : command
  | `(defAlias $name:ident = $body:fnExpr) => do
    let nameStr := toString name.getId
    -- Parse the DSL `fnExpr` body into a `DslExpr` so Rust /
    -- Lean / LaTeX renderers can share the same expression.
    let dslExpr ← parseExpr body.raw
    -- Render the body as Lean source via the DSL's
    -- `DslExpr.toLean`, which strips the struct name from
    -- `mkStruct` and emits anonymous-constructor `⟨…⟩` syntax.
    -- For a top-level `def` Lean can't infer the type of a
    -- bare `⟨…⟩`, so when the user wrote `Name⟨…⟩` at the
    -- outermost level we attach a `: Name` ascription to give
    -- the elaborator a starting type. Inner anonymous
    -- constructors then inherit their expected types from
    -- the outer struct's field types.
    let bodySrc := match dslExpr with
      | .mkStruct sName _ =>
        if sName.isEmpty then DslExpr.toLean dslExpr
        else s!"({DslExpr.toLean dslExpr} : {sName})"
      | _ => DslExpr.toLean dslExpr
    -- Generate `def Name := Body` so the definition is a real
    -- Lean constant — the IDE keeps full hover / gotoDef on
    -- references to `Name`.
    let defStr := s!"def {nameStr} := {bodySrc}"
    let env ← getEnv
    match Parser.runParserCategory env `command defStr with
    | .ok stx =>
      let stx := graftUserNameToken name.getId name.raw stx
      elabCommand stx
    | .error e =>
      throwError s!"defAlias (value): parse error: {e}\n\
        ---\n{defStr}\n---"
    setUserDeclRanges name (← getRef)
    -- After elaboration, look up the constant's inferred type
    -- and convert it to a `DSLType` via `DSLType.parse` over
    -- the pretty-printed type string.
    let env ← getEnv
    let cName := name.getId
    let some cInfo := env.find? cName
      | throwError s!"defAlias (value): could not find {cName} \
          after elaboration"
    let tyStr ← liftCoreM <| Lean.Meta.MetaM.run' do
      let pp ← Lean.Meta.ppExpr cInfo.type
      pure (toString pp)
    let bodyTyTerm ← `(DSLType.parse $(quote tyStr))
    let dslExprTerm : TSyntax `term := quote dslExpr
    let ns : TSyntax `term := quote nameStr
    let adId := mkIdent (cName ++ `aliasDef)
    -- Value aliases name a constant rather than a type, so
    -- the "symbol" is just the constant's name rendered in
    -- monospace (`\mathtt{NAME}` in LaTeX, via `Doc.code`).
    -- `setDoc` doesn't apply to constants — there's no "set
    -- of all values of this type" to name — so leave it as
    -- an empty `MathDoc` (which `checkSymbolUnique` ignores).
    elabCommand (← `(command|
      def $adId : AliasDef :=
        { name := $ns,
          symbolDoc := MathDoc.doc (Doc.code $ns),
          setDoc := MathDoc.raw "",
          docParam := $ns,
          doc := Doc.plain "",
          typeParams := [],
          aliased := $bodyTyTerm,
          value := some $dslExprTerm }))
    let mod ← getMainModule
    let modName : TSyntax `term := quote mod
    elabCommand (← `(command|
      initialize registerAliasDef $adId $modName))
