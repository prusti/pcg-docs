import Core.Dsl.DefProperty
import MIR.Ty

-- Source-side namespace mirrors what the Lean exporter
-- places the generated `IsSized` def under (the first
-- parameter's type, `Ty`). Keeping the names aligned across
-- source and generated lets proofs reference `Ty.IsSized`
-- with one spelling that resolves in both contexts.
namespace Ty

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

end Ty
