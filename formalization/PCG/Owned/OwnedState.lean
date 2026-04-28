import Core.Dsl.DefFn
import Core.Dsl.DefProperty
import Core.Dsl.DefStruct
import MIR.Body
import PCG.Owned.InitTree
import PCG.Owned.OwnedLocal

defStruct OwnedState (.text "os",
    .text "OwnedState")
  "Owned States"
  (.seq [
    .plain "An owned state ",
    Doc.defMath (.text "os")
      (.text "OwnedState"),
    .plain " is the collection of owned locals for a \
     function, one per MIR local, each describing the \
     allocation and initialisation state of that local."])
where
  | locals "Owned locals, one per MIR local."
      : List OwnedLocal
  deriving Repr

defProperty SameLength (.plain "SameLength")
  short (xsDoc, ysDoc) =>
    (.seq [xsDoc, .plain " has the same length as ", ysDoc])
  long (xsDoc, ysDoc) =>
    (.seq [xsDoc, .plain " and ", ysDoc,
           .plain " are owned-local lists of equal length"])
  (xs "The first list of owned locals." : List OwnedLocal)
  (ys "The second list of owned locals." : List OwnedLocal)
  where
  | [] ; [] => true
  | _ :: xs ; _ :: ys => SameLength ‹xs, ys›

-- `open InitTree` so that the unqualified `join` below resolves
-- to `InitTree.join` in source. In the Lean export, `InitTree`
-- is an alias and so receives no namespace; `InitTree.join` is
-- emitted at top level as `join`, where this same call site
-- resolves directly to it without any `open`.
open InitTree

defFn ownedLocalsJoin (.plain "ownedLocalsJoin")
  (.seq [.plain "Pairwise join of two lists of owned locals. \
    For each position, two ", .code "allocated",
    .plain " locals are joined via ", .code "InitTree.join",
    .plain "; any other combination collapses to ",
    .code "unallocated", .plain " — by the deallocation rule \
    of ", .code "join.md",
    .plain ", a local present (allocated) on only one \
    incoming branch must be deallocated after the join."])
  (xs "Owned locals from the first state." : List OwnedLocal)
  (ys "Owned locals from the second state." : List OwnedLocal)
  requires SameLength(xs, ys)
  : List OwnedLocal where
  | [] ; [] => []
  | .allocated x :: xs ; .allocated y :: ys =>
      .allocated ‹join ‹x, y›› :: ownedLocalsJoin ‹xs, ys›
  | _ :: xs ; _ :: ys =>
      .unallocated :: ownedLocalsJoin ‹xs, ys›

namespace OwnedState

defFn join (.plain "join")
  (.seq [.plain "Join two owned states by pairwise joining \
    their owned locals."])
  (os1 "The first owned state." : OwnedState)
  (os2 "The second owned state." : OwnedState)
  : OwnedState :=
    OwnedState⟨ownedLocalsJoin
      ‹os1↦locals, os2↦locals, lean_proof("sorry")›⟩

end OwnedState

namespace Body

defFn initialState (.plain "initialState")
  (.seq [.plain "The initial owned state at the entry of a MIR \
    body. Local 0 (the return place) starts allocated and \
    uninitialised (",
    .math (.bold (.raw "U")),
    .plain "); each argument local (locals 1 through ",
    .code "numArgs",
    .plain ") starts allocated and fully initialised (",
    .math (.bold (.raw "D")),
    .plain "); every other local starts unallocated."])
  (body "The MIR function body." : Body)
  : OwnedState :=
    OwnedState⟨body↦decls·zipIdx·map fun ⟨_, i⟩ =>
      if i == 0 then OwnedLocal.allocated ‹.leaf ‹.uninit››
      else if i ≤ body↦numArgs then
        OwnedLocal.allocated ‹.leaf ‹.deep››
      else OwnedLocal.unallocated⟩

end Body
