import MIR.Ty

defEnum ConstValue (.raw "cv", .cal (.raw "CV"))
  "Constant Values"
  (.plain "A compile-time constant value.")
where
  | bool (val : Bool)
    "A boolean value."
    (.doc (.plain "bool "), #val (.raw "b"))
  | int (val : IntValue)
    "An integer value."
  | tuple (elems : List ConstValue)
    "A tuple value."
    (.doc (.plain "tuple "), #elems (.raw "\\bar{cv}"))
  | array (elems : List ConstValue)
    "An array value."
    (.doc (.plain "array "), #elems (.raw "\\bar{cv}"))
  deriving Repr, BEq, Hashable
