import Core.Dsl.DefStruct
import MIR.Body
import MIR.Place
import OpSem.Pointer

defStruct StackFrame (.raw "\\phi",
    .doc (.plain "StackFrame"))
  "Stack Frames"
  (.seq [
    .plain "A stack frame ",
    Doc.defMath (.raw "\\phi")
      (.doc (.plain "StackFrame")),
    .plain " records the per-call state of a single function \
     activation: the MIR body being executed, the current \
     program counter, and the map from each local of that body \
     to the thin pointer identifying its stack allocation."])
where
  | body "The function body being executed." : Body
  | pc "The current program counter." : Location
  | locals "The per-local thin-pointer allocations."
      : Map Local ThinPointer
  deriving Repr
