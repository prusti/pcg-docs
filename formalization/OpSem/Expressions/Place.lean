import OpSem.Machine
import OpSem.RuntimePlace

namespace Machine

defFn evalLocal (.plain "evalLocal")
  (.seq [.plain "Evaluate a local variable, returning its \
    runtime place. Returns ", .code "None",
    .plain " if the local is dead."])
  (machine "The machine state." : Machine)
  (lcl "The local variable." : Local)
  : Option RuntimePlace begin
  let ptr ← mapGet ‹machine↦locals, lcl›
  return Some (RuntimePlace⟨ptr⟩)

end Machine
