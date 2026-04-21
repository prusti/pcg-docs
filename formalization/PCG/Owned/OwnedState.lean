import Core.Dsl.DefStruct
import PCG.Owned.OwnedLocal

defStruct OwnedState (.doc (.plain "os"),
    .doc (.plain "OwnedState"))
  "Owned States"
  (.seq [
    .plain "An owned state ",
    Doc.defMath (.doc (.plain "os"))
      (.doc (.plain "OwnedState")),
    .plain " is the collection of owned locals for a \
     function, one per MIR local, each describing the \
     allocation and initialisation state of that local."])
where
  | locals "Owned locals, one per MIR local."
      : List OwnedLocal
  deriving Repr
