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
    (.text "init ", #value (.raw "v"))
