import Core.Dsl.DefEnum
import MIR.Ty

defEnum EdgeMutability (.raw "em", .raw "EdgeMutability")
  "Edge Mutabilities"
  (.seq [
    .plain "An edge mutability ",
    Doc.defMath (.raw "em") (.raw "EdgeMutability"),
    .plain " annotates a PCG edge with whether it was \
     introduced by a mutable (", .math (.doc (.code "Mut")),
    .plain ") or immutable/shared (",
    .math (.doc (.code "Imm")),
    .plain ") borrow. It mirrors the ",
    Doc.refLinkOf @Mutability "Mutability",
    .plain " enum used on MIR reference types, named \
     `Mut`/`Imm` to match the terminology used throughout \
     the borrow PCG."])
where
  | mutable
    "Mutable."
    (.doc (.code "Mut"))
  | immutable
    "Immutable (shared)."
    (.doc (.code "Imm"))
  deriving DecidableEq, BEq, Repr, Hashable
