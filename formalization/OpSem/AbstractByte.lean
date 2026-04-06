import Core.Dsl.DefEnum

/- Abstract bytes, derived from the minirust specification:
   https://github.com/minirust/minirust/blob/master/spec/mem/interface.md#abstract-bytes -/

defEnum AbstractByte (.math (.var "b"))
  "Abstract Bytes"
  "An abstract byte in the memory model."
where
  | uninit
    "An uninitialized byte."
    (.doc (.plain "uninit"))
  | init (value : UInt8)
    "An initialized byte with a concrete value."
    (.doc (.plain "init "), #value (.var "v"))
