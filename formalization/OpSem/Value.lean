import MIR.ConstValue

defEnum Value (.raw "v", .cal (.raw "V"))
  "Values"
  "A runtime value."
where
  | bool (val : Bool)
    "A boolean value."
    (.doc (.plain "bool "), #val (.raw "b"))
  | int (val : IntValue)
    "An integer value."
    (.doc (.plain "int "), #val (.raw "iv"))
  | tuple (elems : List Value)
    "A tuple value."
    (.doc (.plain "tuple "), #elems (.raw "\\bar{v}"))
  | array (elems : List Value)
    "An array value."
    (.doc (.plain "array "), #elems (.raw "\\bar{v}"))
  deriving Repr, BEq, Hashable
