import Core.Dsl.DefProperty
import MIR.Ty

defProperty IsSized (.plain "IsSized")
  short
    (doc! "{τ} is a sized type")
  long
    (doc! "{τ} is a primitive (`bool`, `int`), a pointer \
      (`ref`, `box`), or an array of a sized element")
  (τ "The MIR type." : Ty)
  where
  | .bool => true
  | .int _ => true
  | .ref _ _ _ => true
  | .box _ => true
  | .array elem _ => IsSized elem
  | _ => false
