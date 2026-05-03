import Core.Dsl.DefEnum
import Core.Dsl.DefStruct

/- Abstract bytes, based on the minirust definition:
   https://github.com/minirust/minirust/blob/master/spec/mem/interface.md#abstract-bytes -/

defStruct ProvenanceFrag (.raw "pf",
    .text "ProvenanceFrag")
  "Provenance Fragments"
  (doc! "A one-byte provenance fragment $_pf_ ∈ _ProvenanceFrag_$ \
    records the provenance of one byte of an encoded pointer, \
    along with that byte's position within the pointer.")
where
  | provIdx "The allocation index identifying the source pointer's provenance." : Nat
  | position "The position of this byte within the encoded pointer (0–7)." : Nat
  deriving DecidableEq, Repr, Hashable, Inhabited

defEnum AbstractByte (.raw "b",
    .text "Byte")
  "Abstract Bytes"
  (.plain "An abstract byte in the memory model.")
where
  | uninit
    "An uninitialized byte."
  | init (value : UInt8) (provFrag : Option ProvenanceFrag)
    "An initialized byte, optionally with a provenance fragment \
     (when this byte is part of an encoded pointer)."
    (mathdoc! "#init v p")
