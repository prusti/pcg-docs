import Core.Dsl.DefEnum
import MIR.Ty

defEnum EdgeMutability (.raw "em", .raw "EdgeMutability")
  "Edge Mutabilities"
  (doc! "An edge mutability \
    {.math (.seq [(.raw "em"), .sym .setContains, (.raw "EdgeMutability")])} \
    annotates a PCG edge with whether it was introduced by a \
    mutable ({Doc.math (.doc (.code "Mut"))}) or \
    immutable/shared ({Doc.math (.doc (.code "Imm"))}) \
    borrow. It mirrors the #Mutability enum used on MIR \
    reference types, named `Mut`/`Imm` to match the \
    terminology used throughout the borrow PCG.")
where
  | mutable
    "Mutable."
    (.doc (.code "Mut"))
  | immutable
    "Immutable (shared)."
    (.doc (.code "Imm"))
  deriving DecidableEq, BEq, Repr, Hashable
