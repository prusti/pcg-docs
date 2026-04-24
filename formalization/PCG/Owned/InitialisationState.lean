import Core.Dsl.DefEnum
import Core.Dsl.DefFn

defEnum InitialisationState (.raw "i", .raw "I")
  "Initialisation States"
  (.seq [
    .plain "An initialisation state ",
    Doc.defMath (.raw "i") (.raw "I"),
    .plain " describes whether an owned place is \
     uninitialised (",
    .math (.bold (.raw "U")),
    .plain "), shallowly initialised (",
    .math (.bold (.raw "S")),
    .plain "), or fully initialised (",
    .math (.bold (.raw "D")),
    .plain ") at a particular program point. Each leaf node \
     in the initialisation state tree carries one of these \
     values."])
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

defFn join (.plain "join")
  (.seq [
    .plain "Join two initialisation states. This is the leaf \
     case of the initialisation-tree join described in ",
    .code "owned-state.md",
    .plain ": return the minimum of the two states under the \
     order ",
    .math (.bold (.raw "D")), .plain " > ",
    .math (.bold (.raw "S")), .plain " > ",
    .math (.bold (.raw "U")),
    .plain ". In particular, the join is ",
    .math (.bold (.raw "U")),
    .plain " if either side is uninitialised, ",
    .math (.bold (.raw "S")),
    .plain " if one side is shallow and the other is shallow \
     or deep, and ", .math (.bold (.raw "D")),
    .plain " only if both sides are deep."])
  (a "The first state." : InitialisationState)
  (b "The second state." : InitialisationState)
  : InitialisationState where
  | .uninit ; _ => .uninit
  | _ ; .uninit => .uninit
  | .shallow ; _ => .shallow
  | _ ; .shallow => .shallow
  | .deep ; .deep => .deep

/-- The leaf join on `InitialisationState` is commutative:
    `a ∪ b = b ∪ a`. Witnesses the symmetry of the join
    rules documented in `owned-state.md`. -/
theorem join_comm
    (a b : InitialisationState) : join a b = join b a := by
  cases a <;> cases b <;> rfl

end InitialisationState
