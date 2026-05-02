import Core.Dsl.DefEnum
import Core.Dsl.DefFn

defEnum InitialisationState (.raw "i", .raw "I")
  "Initialisation States"
  (doc! "An initialisation state \
    {.math (.seq [.raw "i", .sym .setContains, .raw "I"])} describes whether an \
    owned place is uninitialised ($__U__$), shallowly \
    initialised ($__S__$), or fully initialised ($__D__$) at \
    a particular program point. Each leaf node in the \
    initialisation state tree carries one of these values.")
where
  | uninit
    "Uninitialised or moved-out (no reads are permitted; \
     only writes, to re-initialise the place, are allowed)."
    (.bold (.raw "U"))
  | shallow
    "Shallowly initialised (the place itself holds a valid \
     value, but memory behind a dereference may not be \
     initialised; arises only for `Box`-typed places)."
    (.bold (.raw "S"))
  | deep
    "Fully initialised (all memory reachable from this \
     place, including through dereferences, is valid and \
     accessible)."
    (.bold (.raw "D"))

namespace InitialisationState

defFn meet (.plain "meet")
  (doc! "Meet two initialisation states. This is the leaf \
    case of the initialisation-tree meet described in \
    `owned-state.md`: return the minimum of the two states \
    under the order {Doc.m (.seq [.bold (.raw "D"), .sym .gt, .bold (.raw "S"), .sym .gt, .bold (.raw "U")])}. \
    In particular, the meet is $__U__$ if either side is \
    uninitialised, $__S__$ if one side is shallow and the \
    other is shallow or deep, and $__D__$ only if both sides \
    are deep.")
  (a "The first state." : InitialisationState)
  (b "The second state." : InitialisationState)
  : InitialisationState where
  | .uninit ; _ => .uninit
  | _ ; .uninit => .uninit
  | .shallow ; _ => .shallow
  | _ ; .shallow => .shallow
  | .deep ; .deep => .deep

/-- The leaf meet on `InitialisationState` is commutative:
    `a ∩ b = b ∩ a`. Witnesses the symmetry of the meet
    rules documented in `owned-state.md`. -/
theorem meet_comm
    (a b : InitialisationState) : meet a b = meet b a := by
  cases a <;> cases b <;> rfl

end InitialisationState
