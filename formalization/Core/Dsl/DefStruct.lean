import Core.Registry
import Lean

open Lean in

declare_syntax_cat structField

/-- A field in a `defStruct` declaration:
    `| name doc : Type`, where `doc` is any `Doc`-typed term
    (a string literal coerces to `Doc.plain`).

    The optional `symbol mathDoc` clause overrides the
    automatically-looked-up symbolDoc for the field. Without
    it the field type's own symbolDoc is reused — handy for
    opaque types like `Place`, but ambiguous when several
    fields share a type (e.g. two `Capability` fields both
    rendering as `c`). Use the override to surface the field
    name (or any other math symbol) instead. -/
syntax "| " ident term ":" term ("symbol " term)? : structField

/-- Define a structure with cross-language export metadata.

    Generates:
    1. A Lean `structure` with derived instances
    2. A `.structDef : StructDef` for export

    The long-form description is a `Doc` term, allowing rich
    content (inline code, links, math) rather than a plain string.

    Pass `subscript` before `where` to render the type symbol
    with its type parameters as a subscript in the LaTeX
    presentation (e.g. `rg_D` instead of `rg` for a struct
    parameterised by `D`).

    Example:
    ```
    defStruct RegionVid (.doc (.plain "vid"),
        .doc (.plain "RegionVid"))
      "Region Variables"
      (.plain "A region variable identifier.")
    where
      | id "The region variable id." : Nat
    ``` -/
syntax "defStruct " ident ("{" ident+ "}")?
    "(" term "," term ")"
    str "(" term ")" ("constructor" str)? ("note" str)? ("link" str)?
    ("subscript")?
    " where"
    structField* ("deriving " ident,+)? : command

/-- Extract field name, type, doc, and optional symbolDoc
    override from a `structField` syntax node. -/
private def parseStructField
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM
        (Lean.Ident × Lean.Syntax
         × Lean.TSyntax `term
         × Option (Lean.TSyntax `term)) := do
  match stx with
  | `(structField| | $n:ident $d:term : $t:term
        symbol $sym:term) =>
    pure (n, t, d, some sym)
  | `(structField| | $n:ident $d:term : $t:term) =>
    pure (n, t, d, none)
  | _ => Lean.Elab.throwUnsupportedSyntax

open Lean Elab Command in
/-- Shared elaboration body for the `defStruct` syntax forms.
    `subscriptFlag` controls whether the generated `StructDef`
    has `subscriptTypeParams := true`. -/
private def elabDefStruct
    (name : TSyntax `ident)
    (tps : Option (TSyntaxArray `ident))
    (symDoc setDoc : TSyntax `term)
    (docParam : TSyntax `str)
    (doc : TSyntax `term)
    (ctorName : Option (TSyntax `str))
    (noteLit : Option (TSyntax `str))
    (linkLit : Option (TSyntax `str))
    (subscriptFlag : Bool)
    (fs : TSyntaxArray `structField)
    (derivs : Option (Syntax.TSepArray `ident ","))
    : CommandElabM Unit := do
    let fieldData ← fs.mapM parseStructField
    let typeParamNames : List String := match tps with
      | some ids => ids.toList.map (toString ·.getId)
      | none => []
    let isGeneric := !typeParamNames.isEmpty
    -- Build structure fields using the user's original
    -- type syntax so identifier source positions survive
    -- and editor features like go-to-definition work on
    -- type references inside field declarations.
    let fieldSyntax : Array (TSyntax ``Lean.Parser.Command.structSimpleBinder)
      ← fieldData.mapM fun (fn, ft, _, _) => do
        let ftT : TSyntax `term := ⟨ft⟩
        `(Lean.Parser.Command.structSimpleBinder|
            $fn:ident : $ftT)
    -- `Map K V` / `Set T` expand to `Std.HashMap` /
    -- `Std.HashSet`, whose `κ` / `α` require `BEq` and
    -- `Hashable`. When a generic struct uses either in a
    -- field type — or a generic type already known to
    -- propagate those constraints — emit the same
    -- constraints on every type parameter so the generated
    -- structure type-checks under `autoImplicit := false`.
    let propagating ← hashPropagatingTypes.get
    let typeTokens (s : String) : List String :=
      -- Split on spaces and parens so that `Option
      -- (TransientState P)` produces `["Option",
      -- "TransientState", "P"]`.
      let chars := s.toList.map fun c =>
        if c == '(' || c == ')' then ' ' else c
      String.ofList chars
        |>.splitOn " "
        |>.filter (· != "")
    let fieldsUseHash := fieldData.any fun (_, ft, _, _) =>
      let typeStr :=
        if ft.isIdent then toString ft.getId
        else ft.reprint.getD (toString ft)
      typeTokens typeStr |>.any fun tok =>
        tok == "Map" || tok == "Set" ||
          propagating.contains tok
    -- Type-parameter binders for generic structures. When
    -- fields use `Map` / `Set`, append `[BEq P] [Hashable P]`
    -- instance binders after each `(P : Type)`.
    let tpBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)
      ← typeParamNames.toArray.foldlM
          (init := #[]) fun acc p => do
            let pId := mkIdent (Name.mkSimple p)
            let typeBinder ← `(Lean.Parser.Term.bracketedBinderF|
              ($pId : Type))
            if fieldsUseHash then
              let beq ← `(Lean.Parser.Term.bracketedBinderF|
                [BEq $pId])
              let hash ← `(Lean.Parser.Term.bracketedBinderF|
                [Hashable $pId])
              pure (acc.push typeBinder |>.push beq |>.push hash)
            else
              pure (acc.push typeBinder)
    let deriveNames : Array Ident := match derivs with
      | some ds => ds
      | none =>
        #[mkIdent `DecidableEq, mkIdent `Repr,
          mkIdent `Hashable]
    -- Generic structures embed `deriving` in the
    -- declaration; the monomorphic path uses separate
    -- `deriving instance` commands below.
    if isGeneric then
      let structCmd ← `(command|
        structure $name:ident $tpBinders:bracketedBinder*
          where
        $fieldSyntax:structSimpleBinder*
        deriving $[$deriveNames:ident],*)
      elabCommand structCmd
    else
      let structCmd ← `(command|
        structure $name:ident where
        $fieldSyntax:structSimpleBinder*)
      elabCommand structCmd
      for d in deriveNames do
        elabCommand (← `(command|
          deriving instance $d:ident for $name))
    -- Build StructDef metadata
    let selfN := Name.mkSimple (toString name.getId)
    let fieldDefs ← fieldData.mapM
      fun (fn, ft, fd, fsymOverride) => do
        let ns : TSyntax `term :=
          quote (toString fn.getId)
        let typeStr :=
          if ft.isIdent then toString ft.getId
          else ft.reprint.getD (toString ft)
        let tyTerm ← `(DSLType.parse $(quote typeStr))
        let symTerm : TSyntax `term ← match fsymOverride with
          | some s => `(some ($s : MathDoc))
          | none =>
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
            doc := ($fd : Doc),
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
    let subscriptTerm : TSyntax `term ←
      if subscriptFlag then `(true) else `(false)
    -- Expose `symDoc`, `setDoc`, and `typeParams` as
    -- unhygienic identifiers so user-written doc terms
    -- (and the `defMathSelf` macro) can reference them.
    let symDocId := mkIdent `symDoc
    let setDocId := mkIdent `setDoc
    let typeParamsId := mkIdent `typeParams
    elabCommand (← `(command|
      def $sdId : StructDef :=
        { name := $ns,
          symbolDoc := ($symDoc : MathDoc),
          setDoc := ($setDoc : MathDoc),
          docParam := $docParam,
          doc := (
            let $symDocId : MathDoc := ($symDoc : MathDoc);
            let $setDocId : MathDoc := ($setDoc : MathDoc);
            let $typeParamsId : List String := $typeParamsTerm;
            ($doc : Doc)),
          ctorName := $ctorTerm,
          «note» := $noteTerm,
          «link» := $linkTerm,
          typeParams := $typeParamsTerm,
          subscriptTypeParams := $subscriptTerm,
          fields := $fieldList }))
    let mod ← getMainModule
    let modName : TSyntax `term := quote mod
    elabCommand (← `(command|
      initialize registerStructDef $sdId $modName))
    -- A generic struct that uses `Map`/`Set` (directly or
    -- transitively) propagates `BEq`/`Hashable` constraints
    -- to its type parameters, so anything mentioning this
    -- type as a field component must do likewise. Recorded
    -- in an `initialize` block so the registration survives
    -- across module loads (the IO.Ref state persists through
    -- `import`).
    if isGeneric && fieldsUseHash then
      let nameTerm : TSyntax `term :=
        quote (toString name.getId)
      elabCommand (← `(command|
        initialize registerHashPropagating $nameTerm))

open Lean Elab Command in
elab_rules : command
  | `(defStruct $name:ident $[{ $tps:ident* }]?
       ($symDoc:term, $setDoc:term)
       $docParam:str ($doc:term) $[constructor $ctorName:str]?
       $[note $noteLit:str]? $[link $linkLit:str]? where
       $fs:structField* $[deriving $derivs:ident,*]?)
    => do
    elabDefStruct name tps symDoc setDoc docParam doc
      ctorName noteLit linkLit false fs derivs
  | `(defStruct $name:ident $[{ $tps:ident* }]?
       ($symDoc:term, $setDoc:term)
       $docParam:str ($doc:term) $[constructor $ctorName:str]?
       $[note $noteLit:str]? $[link $linkLit:str]?
       subscript where
       $fs:structField* $[deriving $derivs:ident,*]?)
    => do
    elabDefStruct name tps symDoc setDoc docParam doc
      ctorName noteLit linkLit true fs derivs
