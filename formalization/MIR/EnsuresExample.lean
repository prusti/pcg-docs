import Core.Dsl.DefFn
import Core.Dsl.DefProperty

-- A small demonstration of `ensures` clauses.
--
-- `IsTrue` is a one-place property over `Bool`; `alwaysTrue`
-- is a function whose ensures clause guarantees the result
-- satisfies `IsTrue`. The Lean export wraps the return type
-- as a subtype `{ result : Bool // IsTrue result }`, pairing
-- the actual result with a proof of the postcondition (a
-- `sorry` placeholder).

defProperty IsTrue (.plain "IsTrue")
  short
    (.seq [b, .plain " holds"])
  long
    (.seq [b, .plain " is the boolean value ",
           .code "true"])
  (b "The boolean to test." : Bool)
  where
  | true => true
  | false => false

defFn alwaysTrue (.plain "alwaysTrue")
  (.plain "Returns true unconditionally; the ensures clause \
    states that the result holds.")
  (b "An ignored boolean input." : Bool)
  ensures IsTrue(result)
  : Bool := true
