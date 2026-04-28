import Core.Dsl.DefEnum
import MIR.Place

defEnum TransientState {P}
    (.text "ts", .text "TransientState")
  "Transient States"
  (.seq [
    .plain "A transient state ",
    Doc.defMath (.text "ts")
      (.text "TransientState") ["P"],
    .plain " describes a per-program-point read- or \
     write-borrow side condition tracked by the PCG: either a \
     set of places that are read at this point, or a single \
     place that is the target of an outstanding write borrow \
     (e.g. the borrowed place of a two-phase borrow). The two \
     cases are mutually exclusive: a program point either \
     reads zero or more places or has a single \
     write-borrowed place, but not both."])
where
  | readPlaces (places : Set P)
    "Places read at this program point."
  | writeBorrowedPlace (place : P)
    "The place that is the target of an outstanding write \
     borrow at this program point."
  deriving Repr
