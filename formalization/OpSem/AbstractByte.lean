import Core.Dsl.DefEnum

/- Abstract bytes, derived from the minirust specification:
   https://github.com/minirust/minirust/blob/master/spec/mem/interface.md#abstract-bytes -/

defEnum AbstractByte (.raw "b",
    .text "Byte")
  "Abstract Bytes"
  (.plain "An abstract byte in the memory model.")
where
  | uninit
    "An uninitialized byte."
  | init (value : UInt8)
    "An initialized byte with a concrete value."
    (mathdoc! "#init v")
  | ptrFragment (provIdx : Option Nat) (addr : Nat)
      (offset : Nat)
    "One byte of a pointer value: each fragment redundantly \
     carries the full address and the optional allocation \
     index of the source pointer's provenance, plus its \
     position within the 8-byte pointer encoding (0–7). The \
     redundancy lets `decode` reconstruct the pointer from \
     any single fragment without scanning all eight."
    (mathdoc! "#ptrFragment p a i")
