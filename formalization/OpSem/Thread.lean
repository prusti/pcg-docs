import Core.Dsl.DefStruct
import OpSem.StackFrame

defStruct Thread (.raw "\\theta", .text "Thread")
  "Threads"
  (doc! "A thread \
    $\\theta ∈ _Thread_$ \
    is the execution context of one strand of control flow. \
    Unlike MiniRust we only model a single thread, so the \
    full thread state is the call stack: a list of stack \
    frames whose head is the currently executing activation.")
where
  | stack "The call stack, with the currently executing \
      frame at the head."
      : List StackFrame
  deriving Repr
