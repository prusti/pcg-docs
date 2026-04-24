import Core.Dsl.DefStruct
import OpSem.StackFrame

defStruct Thread (.raw "\\theta", .doc (.plain "Thread"))
  "Threads"
  (.seq [
    .plain "A thread ",
    Doc.defMath (.raw "\\theta")
      (.doc (.plain "Thread")),
    .plain " is the execution context of one strand of \
     control flow. Unlike MiniRust we only model a single \
     thread, so the full thread state is the call stack: a \
     list of stack frames whose head is the currently \
     executing activation."])
where
  | stackFrames "The call stack, with the currently executing \
      frame at the head."
      : List StackFrame
  deriving Repr
