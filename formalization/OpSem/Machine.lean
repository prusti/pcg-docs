import OpSem.Memory
import OpSem.Value
import MIR.Body
import Core.Dsl.DefFn

defStruct Machine (.raw "\\mu", .doc (.plain "Machine"))
  "Machines"
  "A machine state: a function body, program counter, \
   and memory."
where
  | body "The function body." : Body
  | pc "The program counter." : Location
  | mem "The memory." : Memory
  deriving Repr, Hashable

namespace Machine

defFn evalConstant (.plain "evalConstant")
  "Convert a compile-time constant to a runtime value."
  (cv "The constant value." : ConstValue)
  : Value where
  | .bool b => Value.bool‹b›
  | .int iv => Value.int‹iv›
  | .tuple es =>
      Value.tuple‹es ·map fun e => evalConstant‹e››
  | .array es =>
      Value.array‹es ·map fun e => evalConstant‹e››

end Machine
