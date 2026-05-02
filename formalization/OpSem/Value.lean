import MIR.ConstValue
import OpSem.Pointer
import Core.Dsl.DefFn

defEnum Value (.raw "v", .cal (.raw "V"))
  "Values"
  (.seq [
    .plain "A runtime value ",
    .math (.seq [.raw "v", .sym .setContains, .cal (.raw "V")]),
    .plain " is either a boolean, an integer, a tuple, an \
     array, a (data) pointer, or a function pointer."])
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
  | ptr (ptr : ThinPointer)
    "A pointer (the runtime value of a reference or `Box`)."
    (.text "ptr ", #ptr)
  | fnPtr (name : String)
    "A function pointer, naming a function in the program's \
     `functions` map."
    (.text "fn ", #name (.raw "f"))
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
