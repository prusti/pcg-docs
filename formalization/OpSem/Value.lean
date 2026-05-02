import MIR.ConstValue
import OpSem.Pointer
import Core.Dsl.DefFn

defEnum Value (.raw "v", .cal (.raw "V"))
  "Values"
  (doc! "A runtime value \
    $_v_ ∈ \\mathcal\{V}$ \
    is either a boolean, an integer, a tuple, an array, \
    a (data) pointer, or a function pointer.")
where
  | bool (val : Bool)
    "A boolean."
    (mathdoc! "#bool b")
  | int (val : IntValue)
    "An integer."
  | tuple (elems : List Value)
    "A tuple."
    (mathdoc! "#tuple {(MathDoc.raw "\\bar{v}")}")
  | array (elems : List Value)
    "An array."
    (mathdoc! "#array {(MathDoc.raw "\\bar{v}")}")
  | ptr (ptr : ThinPointer)
    "A pointer (the runtime value of a reference or `Box`)."
    (mathdoc! "#ptr {ptr}")
  | fnPtr (name : String)
    "A function pointer, naming a function in the program's \
     `functions` map."
    (mathdoc! "#fn f")
  deriving Repr, BEq, Hashable

defFn valueToPtr (.plain "valueToPtr")
  (doc! "Extract the #ThinPointer from a #Value.ptr. \
    Returns `None` for any other variant.")
  (v "The value." : Value)
  : Option ThinPointer where
  | .ptr p => Some p
  | _ => None

defFn valueToInt (.plain "valueToInt")
  (doc! "Extract the #IntValue from a #Value.int. \
    Returns `None` for any other variant.")
  (v "The value." : Value)
  : Option IntValue where
  | .int iv => Some iv
  | _ => None
