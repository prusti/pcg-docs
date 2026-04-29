import Core.Dsl.DefAlias
import Core.Dsl.DefFn
import Core.Dsl.DefProperty
import MIR.Body
import MIR.Ty
import PCG.Owned.AbstractInitTree
import PCG.Owned.InitialisationState

defAlias InitTree
    (.text "it",
     .text "InitTree")
  "Initialisation Trees"
  (.seq [
    .plain "An initialisation tree ",
    Doc.defMath (.text "it")
      (.text "InitTree"),
    .plain " describes the initialisation state of an owned \
     place: an abstract initialisation tree whose leaves each \
     carry an initialisation state. By invariant, an internal \
     node has at least one descendant leaf that is not fully \
     initialised (otherwise the subtree collapses to a single ",
    .math (.bold (.raw "D")),
    .plain " leaf), and every place reachable from the root \
     of the tree is owned — so any ",
    .math (.doc (.code "*")),
    .plain " step in the tree is a dereference of a ",
    .code "Box",
    .plain "-typed place rather than a reference."])
  := AbstractInitTree InitialisationState

defProperty HasNonDeepLeaf (.plain "HasNonDeepLeaf")
  short (itDoc) =>
    (.seq [itDoc, .plain " has at least one non-deep leaf"])
  long (itDoc) =>
    (.seq [itDoc, .plain " contains at least one descendant \
           leaf whose capability is not fully initialised — \
           recurses structurally on the tree, with the ",
           .code "fields",
           .plain " case folded over the children list as a \
           disjunction."])
  (it "The initialisation tree." : InitTree)
  := match it with
     | .leaf cap => cap ≠ .deep
     | .internal (.fields []) => false
     | .internal (.fields (⟨_, _, sub⟩ :: rest)) =>
         HasNonDeepLeaf ‹sub› ∨
         HasNonDeepLeaf ‹.internal ‹.fields ‹rest›››
     | .internal (.deref d) => HasNonDeepLeaf ‹d›
     | .internal (.guided (.downcast _ d)) =>
         HasNonDeepLeaf ‹d›
     | .internal (.guided (.constantIndex _ d)) =>
         HasNonDeepLeaf ‹d›
     | .internal (.guided (.index _ d)) =>
         HasNonDeepLeaf ‹d›
     | .internal (.guided (.subslice _ _ _ d)) =>
         HasNonDeepLeaf ‹d›
     end

defFnMutual
defFn itPlaces (.plain "itPlaces")
  (.seq [.plain "All MIR places reached by walking an \
    initialisation tree from a base local along an accumulated \
    projection. Each leaf contributes a single place; internal \
    nodes extend the projection with the corresponding ",
    .code "ProjElem",
    .plain " step. Constant-index and subslice guided \
    expansions have no ", .code "ProjElem",
    .plain " counterpart and leave the projection unchanged."])
  (it "The initialisation tree." : InitTree)
  (base "The base local the tree is rooted at." : Local)
  (projAcc "The projection accumulated so far, from the root."
      : List ProjElem)
  : Set Place where
  | .leaf _ ; base ; projAcc =>
      ⦃ Place⟨base, projAcc⟩ ⦄
  | .internal (.fields fs) ; base ; projAcc =>
      placesFromFields ‹fs, base, projAcc›
  | .internal (.deref d) ; base ; projAcc =>
      itPlaces ‹d, base, projAcc ++ [ProjElem.deref]›
  | .internal (.guided (.downcast v d)) ; base ; projAcc =>
      itPlaces ‹d, base,
        projAcc ++ [ProjElem.downcast ‹v›]›
  | .internal (.guided (.constantIndex _ d)) ; base ; projAcc =>
      itPlaces ‹d, base, projAcc›
  | .internal (.guided (.index l d)) ; base ; projAcc =>
      itPlaces ‹d, base,
        projAcc ++ [ProjElem.index ‹l›]›
  | .internal (.guided (.subslice _ _ _ d)) ; base ; projAcc =>
      itPlaces ‹d, base, projAcc›
defFn placesFromFields (.plain "placesFromFields")
  (.seq [.plain "Helper for ", .code "itPlaces",
    .plain ": collect places from every child of a ",
    .code "fields", .plain " expansion, prefixing each \
    child's path with its field step."])
  (fs "Children of a fields expansion."
      : List (FieldIdx × Ty × InitTree))
  (base "The base local the tree is rooted at." : Local)
  (projAcc "The projection accumulated so far, from the root."
      : List ProjElem)
  : Set Place where
  | [] ; _ ; _ => ∅
  | ⟨fi, ty, sub⟩ :: rest ; base ; projAcc =>
      let fldPlaces := itPlaces ‹sub, base, projAcc ++ [ProjElem.field ‹fi, ty›]›;
      placesFromFields ‹rest, base, projAcc›
end

defFn places (.plain "places")
  (.seq [.plain "All MIR places covered by an initialisation \
    tree rooted at a given base local, with the empty \
    projection."])
  (it "The initialisation tree." : InitTree)
  (base "The base local the tree is rooted at." : Local)
  : Set Place :=
    itPlaces ‹it, base, []›

/-- Ownership of a place in a body, bundled with the
    `validPlace` precondition so it is precondition-free. -/
def placeIsOwnedIn (body : Body) (p : Place) : Prop :=
  ∃ h : validPlace body p, isOwned body p h = true

defProperty AllPlacesOwned (.plain "AllPlacesOwned")
  short (bodyDoc, baseDoc, itDoc) =>
    (.seq [.plain "every place in ", itDoc,
           .plain " (rooted at ", baseDoc,
           .plain ") is owned in ", bodyDoc])
  long (bodyDoc, baseDoc, itDoc) =>
    (.seq [.plain "every place reachable by walking ",
           itDoc, .plain " from base local ", baseDoc,
           .plain " is an owned place in body ", bodyDoc])
  (body "The MIR function body." : Body)
  (base "The base local the tree is rooted at." : Local)
  (it "The initialisation tree." : InitTree)
  :=
    places ‹it, base› ·forAll fun p =>
      placeIsOwnedIn ‹body, p›

defProperty ValidInitTree (.plain "ValidInitTree")
  short (bodyDoc, baseDoc, itDoc) =>
    (.seq [itDoc,
           .plain " is a valid initialisation tree rooted \
           at ", baseDoc, .plain " in body ", bodyDoc])
  long (bodyDoc, baseDoc, itDoc) =>
    (.seq [itDoc, .plain " has at least one non-deep \
           leaf, and every place reachable by walking ",
           itDoc, .plain " from base local ", baseDoc,
           .plain " is an owned place in body ", bodyDoc])
  (body "The MIR function body." : Body)
  (base "The base local the tree is rooted at." : Local)
  (it "The initialisation tree." : InitTree)
  :=
    HasNonDeepLeaf ‹it› ∧ AllPlacesOwned ‹body, base, it›

namespace InitTree

defFn join (.plain "join")
  (.seq [
    .plain "Join two initialisation trees, implementing the \
     recursive join of ",
    .code "owned-state.md", .plain ". At matching leaves we \
     take the minimum via ", .code "InitialisationState.join",
    .plain ". When one side is a leaf and the other is \
     internal, the uninitialised/shallow leaf dominates (its \
     initialisation state covers every descendant place), \
     while a fully-initialised leaf yields to the more \
     precise internal expansion. When both sides are ",
    .code "deref", .plain " nodes we recurse on the child. \
     Other internal/internal cases (",
    .code "fields", .plain " against ", .code "fields", .plain ", \
     mismatched expansion shapes, or ", .code "guided",
    .plain " expansions) conservatively collapse to ",
    .math (.bold (.raw "U")),
    .plain "; a faithful pointwise handling of those cases is \
     a follow-up."])
  (a "The first tree." : InitTree)
  (b "The second tree." : InitTree)
  : InitTree where
  -- Leaf + Leaf: take the minimum initialisation state.
  | .leaf x ; .leaf y =>
      .leaf ‹InitialisationState.join ‹x, y››
  -- Leaf U vs Internal (either side): U dominates.
  | .leaf (.uninit) ; .internal _ => .leaf ‹.uninit›
  | .internal _ ; .leaf (.uninit) => .leaf ‹.uninit›
  -- Leaf S vs Internal (either side): S dominates.
  | .leaf (.shallow) ; .internal _ => .leaf ‹.shallow›
  | .internal _ ; .leaf (.shallow) => .leaf ‹.shallow›
  -- Leaf D vs Internal: the internal expansion wins.
  | .leaf (.deep) ; .internal xp => .internal ‹xp›
  | .internal xp ; .leaf (.deep) => .internal ‹xp›
  -- Matching `.deref` internals: recurse on the child.
  | .internal (.deref a) ; .internal (.deref b) =>
      .internal ‹.deref ‹join ‹a, b›››
  -- Other internal / internal combinations: conservative.
  | .internal _ ; .internal _ => .leaf ‹.uninit›

/-- The initialisation-tree join is commutative:
    `join a b = join b a`. Case analysis reduces nearly every
    branch to `rfl`; the matching-leaf branch follows from
    `InitialisationState.join_comm`, and the matching
    `.deref` branch reduces by structural recursion. -/
theorem join_comm
    : ∀ (a b : InitTree), join a b = join b a
  | .leaf x, .leaf y => by
      simp only [join, InitialisationState.join_comm]
  | .leaf .uninit, .internal _ => rfl
  | .internal _, .leaf .uninit => rfl
  | .leaf .shallow, .internal _ => rfl
  | .internal _, .leaf .shallow => rfl
  | .leaf .deep, .internal _ => rfl
  | .internal _, .leaf .deep => rfl
  | .internal (.deref a), .internal (.deref b) => by
      simp only [join, join_comm a b]
  | .internal (.deref _), .internal (.fields _) => rfl
  | .internal (.deref _), .internal (.guided _) => rfl
  | .internal (.fields _), .internal (.deref _) => rfl
  | .internal (.fields _), .internal (.fields _) => rfl
  | .internal (.fields _), .internal (.guided _) => rfl
  | .internal (.guided _), .internal (.deref _) => rfl
  | .internal (.guided _), .internal (.fields _) => rfl
  | .internal (.guided _), .internal (.guided _) => rfl
termination_by a _ => sizeOf a

end InitTree
