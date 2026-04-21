import Core.Registry
import Lean

open Lean in

declare_syntax_cat structField

/-- A field in a `defStruct` declaration:
    `| name doc : Type`, where `doc` is any `Doc`-typed term
    (a string literal coerces to `Doc.plain`). -/
syntax "| " ident term ":" term : structField

/-- Define a structure with cross-language export metadata.

    Generates:
    1. A Lean `structure` with derived instances
    2. A `.structDef : StructDef` for export

    The long-form description is a `Doc` term, allowing rich
    content (inline code, links, math) rather than a plain string.

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
    " where"
    structField* ("deriving " ident,+)? : command

/-- Extract field name, type, and doc from a `structField`
    syntax node. -/
private def parseStructField
    (stx : Lean.Syntax)
    : Lean.Elab.Command.CommandElabM
        (Lean.Ident × Lean.Syntax
         × Lean.TSyntax `term) := do
  match stx with
  | `(structField| | $n:ident $d:term : $t:term) =>
    pure (n, t, d)
  | _ => Lean.Elab.throwUnsupportedSyntax

open Lean Elab Command in
elab_rules : command
  | `(defStruct $name:ident $[{ $tps:ident* }]?
       ($symDoc:term, $setDoc:term)
       $docParam:str ($doc:term) $[constructor $ctorName:str]?
       $[note $noteLit:str]? $[link $linkLit:str]? where
       $fs:structField* $[deriving $derivs:ident,*]?)
    => do
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
      ← fieldData.mapM fun (fn, ft, _) => do
        let ftT : TSyntax `term := ⟨ft⟩
        `(Lean.Parser.Command.structSimpleBinder|
            $fn:ident : $ftT)
    -- `Map K V` / `Set T` expand to `Std.HashMap` /
    -- `Std.HashSet`, whose `κ` / `α` require `BEq` and
    -- `Hashable`. When a generic struct uses either in a
    -- field type, emit the same constraints on every type
    -- parameter so the generated structure type-checks under
    -- `autoImplicit := false`.
    let fieldsUseHash := fieldData.any fun (_, ft, _) =>
      let typeStr :=
        if ft.isIdent then toString ft.getId
        else ft.reprint.getD (toString ft)
      typeStr.splitOn " " |>.any fun tok =>
        tok == "Map" || tok == "Set"
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
      fun (fn, ft, fd) => do
        let ns : TSyntax `term :=
          quote (toString fn.getId)
        let typeStr :=
          if ft.isIdent then toString ft.getId
          else ft.reprint.getD (toString ft)
        let tyTerm ← `(DSLType.parse $(quote typeStr))
        let symTerm : TSyntax `term ←
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
    elabCommand (← `(command|
      def $sdId : StructDef :=
        { name := $ns,
          symbolDoc := ($symDoc : MathDoc),
          setDoc := ($setDoc : MathDoc),
          docParam := $docParam,
          doc := ($doc : Doc),
          ctorName := $ctorTerm,
          «note» := $noteTerm,
          «link» := $linkTerm,
          typeParams := $typeParamsTerm,
          fields := $fieldList }))
    let mod ← getMainModule
    let modName : TSyntax `term := quote mod
    elabCommand (← `(command|
      initialize registerStructDef $sdId $modName))
