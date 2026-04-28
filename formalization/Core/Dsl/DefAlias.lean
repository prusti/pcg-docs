import Core.Registry
import Lean

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

open Lean Elab Command in
elab_rules : command
  | `(defAlias $name:ident $[{ $tps:ident* }]?
       ($symDoc:term, $setDoc:term)
       $docParam:str ($doc:term) := $body:term)
    => do
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
    | .ok stx => elabCommand stx
    | .error e =>
      throwError s!"defAlias: parse error: {e}\n\
        ---\n{abbrevStr}\n---"
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
          aliased := $bodyTyTerm }))
    let mod ← getMainModule
    let modName : TSyntax `term := quote mod
    elabCommand (← `(command|
      initialize registerAliasDef $adId $modName))
