import MIR.ConstValue

defEnum Value (.raw "v", .cal (.raw "V"))
  "Values"
  (.seq [
    .plain "A runtime value ",
    Doc.defMath (.raw "v") (.cal (.raw "V")),
    .plain " is either a boolean, an integer, a tuple, or \
     an array."])
where
  | bool (val : Bool)
    "A boolean."
    (.text "bool ", #val (.raw "b"))
  | int (val : IntValue)
    "An integer."
  | tuple (elems : List Value)
    "A tuple."
    (.text "tuple ", #elems (.raw "\\bar{v}"))
  | array (elems : List Value)
    "An array."
    (.text "array ", #elems (.raw "\\bar{v}"))
  deriving Repr, BEq, Hashable
