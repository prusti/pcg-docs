import MIR.Ty

defEnum ConstValue (.raw "cv", .cal (.raw "CV"))
  "Constant Values"
  (.plain "A compile-time constant value.")
where
  | bool (val : Bool)
    "A boolean value."
    (.text "bool ", #val (.raw "b"))
  | int (val : IntValue)
    "An integer value."
  | tuple (elems : List ConstValue)
    "A tuple value."
    (.text "tuple ", #elems (.raw "\\bar{cv}"))
  | array (elems : List ConstValue)
    "An array value."
    (.text "array ", #elems (.raw "\\bar{cv}"))
  | fnPtr (name : String)
    "A function pointer, naming a function in the program's \
     `functions` map."
    (.text "fn ", #name (.raw "f"))
  deriving Repr, BEq, Hashable
