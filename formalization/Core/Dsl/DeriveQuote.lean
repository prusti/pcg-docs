import Lean

/-!
# `deriving Lean.Quote` handler

Registers a deriving handler for `Lean.Quote` (the typeclass used by
`` `($x) `` and `macro_rules` to splice values into syntax) so that
inductive types can write `deriving Quote` instead of hand-rolling a
`partial def quoteT` and an `instance : Quote T where quote := quoteT`.

For a constructor `T.c : α₁ → … → αₙ → T`, the generated instance
produces

```
Lean.Syntax.mkApp (Lean.mkIdent ``T.c) #[q₁, …, qₙ]
```

where each `qᵢ` is:

* a direct recursive call to the auxiliary function when `αᵢ` is `T`
  (so structurally-smaller fields avoid a detour through typeclass
  resolution);
* `Lean.Quote.quote aᵢ` otherwise (delegating to an existing `Quote αᵢ`
  instance — e.g. `Quote String`, `Quote Nat`, `Quote (List α)`).

The auxiliary function is generated `partial`; recursion through
non-trivial containers relies on the local `Quote T` binding installed
by `mkLocalInstanceLetDecls`.
-/

namespace Core.Deriving.Quote

open Lean Elab Parser.Term Meta Command Deriving

/-- Body of the generated auxiliary function: a `match` on the target
    with one arm per constructor. -/
def mkBody (header : Header) (indVal : InductiveVal) (auxFunName : Name) :
    TermElabM Term := do
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts
  `(match $[$discrs],* with $alts:matchAlt*)
where
  mkAlts : TermElabM (Array (TSyntax ``matchAlt)) := do
    let mut alts := #[]
    for ctorName in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      let alt ← forallTelescopeReducing ctorInfo.type fun xs _ => do
        let mut patterns := #[]
        for _ in *...indVal.numIndices do
          patterns := patterns.push (← `(_))
        let mut ctorArgs : Array Term := #[]
        let mut rhsArgs : Array Term := #[]
        for h : i in *...xs.size do
          let x := xs[i]
          if i < indVal.numParams then
            ctorArgs := ctorArgs.push (← `(_))
          else
            let a := mkIdent (← mkFreshUserName `a)
            ctorArgs := ctorArgs.push a
            if (← inferType x).isAppOf indVal.name then
              rhsArgs := rhsArgs.push
                (← `($(mkIdent auxFunName):ident $a:ident))
            else
              rhsArgs := rhsArgs.push (← `(Lean.Quote.quote $a:ident))
        patterns := patterns.push
          (← `(@$(mkIdent ctorName):ident $ctorArgs:term*))
        let rhs ←
          `(Lean.Syntax.mkApp (Lean.mkIdent $(quote ctorInfo.name))
              #[$[$rhsArgs],*])
        `(matchAltExpr| | $[$patterns:term],* => $rhs)
      alts := alts.push alt
    return alts

/-- The auxiliary `partial def` generated for each type of a
    (possibly mutual) inductive. -/
def mkAuxFunction (ctx : Deriving.Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indVal := ctx.typeInfos[i]!
  let header ← mkHeader ``Lean.Quote 1 indVal
  let letDecls ← mkLocalInstanceLetDecls ctx ``Lean.Quote header.argNames
  let body ← mkLet letDecls (← mkBody header indVal auxFunName)
  let binders := header.binders
  `(partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* :
      Lean.TSyntax `term := $body:term)

def mkMutualBlock (ctx : Deriving.Context) : TermElabM Syntax := do
  let mut auxDefs := #[]
  for i in *...ctx.typeInfos.size do
    auxDefs := auxDefs.push (← mkAuxFunction ctx i)
  `(mutual $auxDefs:command* end)

private def mkQuoteInstanceCmd (declName : Name) : TermElabM (Array Syntax) := do
  -- Quote instances are always emitted as `partial`, so tell `mkContext`
  -- we do not want structural recursion even for non-nested recursive
  -- inductives.
  let ctx ← mkContext ``Lean.Quote "quote" declName (supportsRec := false)
  let cmds := #[← mkMutualBlock ctx] ++
    (← mkInstanceCmds ctx ``Lean.Quote #[declName])
  return cmds

/-- Entry point registered as a deriving handler for `Lean.Quote`. -/
def mkQuoteInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for declName in declNames do
      let cmds ← liftTermElabM <| mkQuoteInstanceCmd declName
      cmds.forM elabCommand
    return true
  else
    return false

initialize
  registerDerivingHandler ``Lean.Quote mkQuoteInstanceHandler

end Core.Deriving.Quote
