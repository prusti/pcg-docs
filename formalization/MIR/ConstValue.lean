import MIR.Ty

defEnum ConstValue (.raw "cv", .cal (.raw "CV"))
  "Constant Values"
  (.plain "A compile-time constant value.")
where
  | bool (val : Bool)
    "A boolean value."
    (mathdoc! "#bool b")
  | int (val : IntValue)
    "An integer value."
  | tuple (elems : List ConstValue)
    "A tuple value."
    (mathdoc! "#tuple {(MathDoc.raw "\\bar{cv}")}")
  | array (elems : List ConstValue)
    "An array value."
    (mathdoc! "#array {(MathDoc.raw "\\bar{cv}")}")
  | fnPtr (name : String)
    "A function pointer, naming a function in the program's \
     `functions` map."
    (mathdoc! "#fn f")
  deriving Repr, BEq, Hashable
