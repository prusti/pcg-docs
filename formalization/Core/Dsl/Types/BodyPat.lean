import Core.Export.Latex
import Core.Dsl.DeriveQuote

/-- A pattern in a function body. -/
inductive BodyPat where
  | wild
  | var (name : String)
  | ctor (name : String) (args : List BodyPat)
  /-- Empty list pattern: `[]`. -/
  | nil
  /-- List cons pattern: `h :: t`. -/
  | cons (head : BodyPat) (tail : BodyPat)
  /-- Numeric literal pattern. -/
  | natLit (n : Nat)
  deriving Repr, Inhabited, Lean.Quote

-- ══════════════════════════════════════════════
-- Doc rendering
-- ══════════════════════════════════════════════

/-- Intercalate a separator between math doc fragments. -/
def mathIntercalate (sep : MathDoc)
    : List MathDoc → MathDoc
  | [] => .seq []
  | [m] => m
  | ms => .seq (ms.intersperse sep)

namespace BodyPat

/-- Render a constructor name as a hyperlinked, dashed-underlined
    reference when it resolves to a known variant. Accepts either
    short (`int`) or qualified (`Value.int`) forms; the anchor
    always uses the fully-qualified form (e.g. `ctor:Value.int`)
    so that variants with the same short name in different enums
    do not collide. -/
def ctorRef
    (resolveCtor : String → Option String) (n : String) : MathDoc :=
  match resolveCtor n with
  | some qualified =>
    .doc (.link (.underline .dashed (.plain n))
      s!"#ctor:{qualified}")
  | none => MathDoc.text n

partial def toDoc
    (ctorDisplay : String → Option MathDoc)
    (resolveCtor : String → Option String := fun _ => none)
    : BodyPat → MathDoc
  | .wild => .sym .underscore
  | .var n => .raw n
  | .ctor "⟨⟩" args =>
    MathDoc.paren (mathIntercalate (.sym .comma)
      (args.map (toDoc ctorDisplay resolveCtor)))
  | .ctor n args =>
    if args.isEmpty then
      match ctorDisplay n with
      | some display => display
      | none => ctorRef resolveCtor n
    else
      let argParts :=
        args.map (toDoc ctorDisplay resolveCtor)
      .seq [ ctorRef resolveCtor n
           , MathDoc.paren
               (mathIntercalate (.sym .comma) argParts) ]
  | .nil => MathDoc.bracket (.seq [])
  | .cons h t =>
    let rec flatten : BodyPat → Option (List BodyPat)
      | .nil => some []
      | .cons h t => (flatten t).map (h :: ·)
      | _ => none
    match flatten (.cons h t) with
    | some elems =>
      MathDoc.bracket (mathIntercalate (.sym .comma)
        (elems.map (toDoc ctorDisplay resolveCtor)))
    | none =>
      .seq [ h.toDoc ctorDisplay resolveCtor
           , .sym .cons
           , t.toDoc ctorDisplay resolveCtor ]
  | .natLit n => .raw (toString n)

end BodyPat
