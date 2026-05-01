import Lean
import Core.Dsl.DeriveQuote

/-- A presentation-only formatting hint attached to a DSL
    sub-expression. Consumed by the LaTeX renderer; the Lean
    and Rust exporters pass the wrapped expression through
    unchanged.

    Hints describe layout decisions that are visual but
    syntactically irrelevant — they introduce no new value
    or proof obligation in the generated Lean. -/
inductive FormatHint where
  /-- Insert a soft line break before the wrapped expression.
      The LaTeX backend lifts the enclosing math sequence to
      a single-column array environment so the break renders
      as an actual line. -/
  | break_
  /-- Indent the wrapped expression by `n` half-em units. -/
  | indent (n : Nat)
  /-- Soft break followed by indentation on the new line. -/
  | breakIndent (n : Nat)
  /-- Insert a soft line break *after* the wrapped expression.
      Emitted when the user wrote `‹break›` immediately before
      an operator (`a ‹break› → b`, `a ‹break› ∧ b`): the
      break attaches to the left operand so the rendered form
      starts the next line with the operator (`a ⏎ → b`)
      rather than starting it with the right operand
      (`a → ⏎ b`, the layout produced by the prefix form
      `a → ‹break› b`). -/
  | breakAfter
  deriving Repr, Inhabited, Lean.Quote
