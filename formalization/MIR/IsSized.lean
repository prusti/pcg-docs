import Core.Dsl.DefProperty
import MIR.Ty

defProperty IsSized (.plain "IsSized")
  short
    (.seq [τ, .plain " is a sized type"])
  long
    (.seq [τ, .plain " is a primitive (",
           .code "bool", .plain ", ", .code "int",
           .plain "), a pointer (", .code "ref",
           .plain ", ", .code "box", .plain "), or an \
           array of a sized element"])
  (τ "The MIR type." : Ty)
  where
  | .bool => true
  | .int _ => true
  | .ref _ _ _ => true
  | .box _ => true
  | .array elem _ => IsSized ‹elem›
  | _ => false
