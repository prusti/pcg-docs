import OpSem.Memory
import OpSem.Program
import OpSem.RuntimePlace
import OpSem.Thread
import OpSem.Value
import OpSem.Decode
import MIR.Body
import Core.Dsl.DefFn

defStruct Machine (.raw "\\mu", .doc (.plain "Machine"))
  "Machines"
  (.seq [
    .plain "A machine state ",
    Doc.defMath (.raw "\\mu") (.doc (.plain "Machine")),
    .plain " bundles the whole program being executed, the \
     single-threaded execution context, and the shared memory. \
     Per-call state — the function body, program counter, and \
     local pointer map — lives on the thread's current stack \
     frame."])
where
  | program "The program being executed." : Program
  | thread "The single thread of execution." : Thread
  | mem "The memory." : Memory
  deriving Repr

namespace Machine

defFn currentFrame (.plain "currentFrame")
  (.plain "The currently executing stack frame, i.e. the head \
    of the thread's call stack.")
  (m "The machine state." : Machine)
  : Option StackFrame :=
    m↦thread↦stackFrames·head?

defFn evalConstant (.plain "evalConstant")
  (.plain "Convert a compile-time constant to a runtime value.")
  (cv "The constant value." : ConstValue)
  : Value where
  | .bool b => Value.bool‹b›
  | .int iv => Value.int‹iv›
  | .tuple es =>
      Value.tuple‹es ·map evalConstant›
  | .array es =>
      Value.array‹es ·map evalConstant›

defFn typedLoad (.plain "typedLoad")
  (.seq [.plain "Load a value of the given type from \
    memory at the given pointer. Returns ", .code "None",
    .plain " if the pointer is invalid or the bytes \
    cannot be decoded."])
  (m "The memory." : Memory)
  (ptr "The pointer." : ThinPointer)
  (ty "The type to load." : Ty)
  : Option Value begin
  let sz ← Ty.bytes ‹ty›
  let rawBytes := Memory.load ‹m, ptr, sz›
  return decode ‹ty, rawBytes›

defFn typedStore (.plain "typedStore")
  (.plain "Store a value into memory at the given pointer. \
   Encodes the value as bytes and writes them to memory.")
  (m "The memory." : Memory)
  (ptr "The pointer." : ThinPointer)
  (v "The value to store." : Value)
  : Memory :=
    Memory.store ‹m, ptr, encode ‹v››

end Machine
