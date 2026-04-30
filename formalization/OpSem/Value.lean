import MIR.ConstValue
import OpSem.Pointer

defEnum Value (.raw "v", .cal (.raw "V"))
  "Values"
  (.seq [
    .plain "A runtime value ",
    Doc.defMath (.raw "v") (.cal (.raw "V")),
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
