import Core.Dsl.DefEnum
import OpSem.Machine

defEnum ExecutionResult (.raw "er", .text "ExecutionResult")
  "Execution Results"
  (doc! "An execution result \
    {.math (.seq [(.raw "er"), .sym .setContains, (.text "ExecutionResult")])} \
    summarises the terminal status of a program: either it \
    ran to completion (`success`) or it stopped abnormally \
    (`error`).")
where
  | success
    "The program ran to completion."
  | error
    "The program halted abnormally."
  deriving Repr, BEq, Hashable

defEnum StepResult (.raw "sr", .text "StepResult")
  "Step Results"
  (doc! "The outcome of a single execution step. `done` indicates that the program has finished, \
    carrying an #ExecutionResult describing how it ended; `ok` indicates that the step produced a \
    new machine state and execution should continue.")
  long where
  | done (result : ExecutionResult)
    "The program has finished with the given result."
  | ok (machine : Machine)
    "The step produced a new machine state."
  deriving Repr
