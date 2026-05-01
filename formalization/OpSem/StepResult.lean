import Core.Dsl.DefEnum
import OpSem.Machine

defEnum ExecutionResult (.raw "er", .text "ExecutionResult")
  "Execution Results"
  (.seq [.plain "An execution result ",
    Doc.defMath (.raw "er")
      (.text "ExecutionResult"),
    .plain " summarises the terminal status of a program: \
      either it ran to completion (",
    .code "success", .plain ") or it stopped abnormally (",
    .code "error", .plain ")."])
where
  | success
    "The program ran to completion."
  | error
    "The program halted abnormally."
  deriving Repr, BEq, Hashable

defEnum StepResult (.raw "sr", .text "StepResult")
  "Step Results"
  (.seq [.plain "The outcome of a single execution step. ",
    .code "done", .plain " indicates that the program has \
      finished, carrying an ", Doc.refLinkOf @ExecutionResult "ExecutionResult",
    .plain " describing how it ended; ", .code "ok",
    .plain " indicates that the step produced a new machine \
      state and execution should continue."])
  long where
  | done (result : ExecutionResult)
    "The program has finished with the given result."
  | ok (machine : Machine)
    "The step produced a new machine state."
  deriving Repr
