import OpSem.Machine
import OpSem.RuntimePlace

/-- Look up a key in a HashMap. -/
def mapGet {κ : Type} [BEq κ] [Hashable κ] {ν : Type}
    (m : Map κ ν) (k : κ) : Option ν :=
  m.get? k

namespace Machine

defFn evalLocal (.plain "evalLocal")
  "Evaluate a local variable, returning its runtime \
   place. Returns `None` if the local is dead."
  (machine "The machine state." : Machine)
  (lcl "The local variable." : Local)
  : Option RuntimePlace begin
  let ptr ← mapGet ‹machine↦locals, lcl›
  return Some (RuntimePlace⟨ptr⟩)

end Machine
