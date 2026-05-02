import Core.Dsl.DefAlias
import Core.Dsl.DefFn
import Core.Dsl.DefProperty
import Core.Dsl.DefRaw
import MIR.Body
import MIR.Ty
import PCG.Owned.AbstractInitTree
import PCG.Owned.InitialisationState

defAlias InitTree
    (.text "it",
     .text "InitTree")
  "Initialisation Trees"
  (doc! "An initialisation tree \
    {Doc.defMath (.text "it") (.text "InitTree")} describes \
    the initialisation state of an owned place: an abstract \
    initialisation tree whose leaves each carry an \
    initialisation state. By invariant, an internal node has \
    at least one descendant leaf that is not fully \
    initialised (otherwise the subtree collapses to a single \
    {Doc.m (.bold (.raw "D"))} leaf), and every place \
    reachable from the root of the tree is owned — so any \
    {Doc.m (.doc (.code "*"))} step in the tree is a \
    dereference of a `Box`-typed place rather than a \
    reference.")
  := AbstractInitTree InitialisationState

defProperty HasNonDeepLeaf (.plain "HasNonDeepLeaf")
  short
    (doc! "{it} has at least one non-deep leaf")
  long
    (doc! "{it} contains at least one descendant leaf whose \
      capability is not fully initialised — recurses \
      structurally on the tree, with the `fields` case \
      folded over the children list as a disjunction.")
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
  (doc! "All MIR places reached by walking an initialisation tree from a base local along an \
    accumulated projection. Each leaf contributes a single place; internal nodes extend the \
    projection with the corresponding #ProjElem step. Constant-index and subslice guided expansions \
    have no #ProjElem counterpart and leave the projection unchanged.")
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
  (doc! "Helper for #itPlaces: collect places from every child of a `fields` expansion, prefixing \
    each child's path with its field step.")
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
  (doc! "All MIR places covered by an initialisation tree rooted at a given base local, with the \
    empty projection.")
  (it "The initialisation tree." : InitTree)
  (base "The base local the tree is rooted at." : Local)
  : Set Place :=
    itPlaces ‹it, base, []›

-- The DSL has no surface syntax for an unconditional bundled
-- `Prop` helper that hides a `validPlace` precondition, so
-- it sits in a `defRaw` block: the inner declaration is real
-- Lean (the IDE keeps full highlighting / hover / gotoDef on
-- it) and the export pipeline picks the verbatim source up
-- via `getRegisteredRawBlocks`.
defRaw middle =>
def placeIsOwnedIn (body : Body) (p : Place) : Prop :=
  ∃ h : validPlace body p, isOwned body p h = true

defProperty AllPlacesOwned (.plain "AllPlacesOwned")
  short
    (doc! "every place in {it} (rooted at {base}) is owned \
      in {body}")
  long
    (doc! "every place reachable by walking {it} from base \
      local {base} is an owned place in body {body}")
  (body "The MIR function body." : Body)
  (base "The base local the tree is rooted at." : Local)
  (it "The initialisation tree." : InitTree)
  :=
    places ‹it, base› ·forAll fun p =>
      placeIsOwnedIn ‹body, p›

defProperty ValidInitTree (.plain "ValidInitTree")
  short
    (doc! "{it} is a valid initialisation tree rooted at \
      {base} in body {body}")
  long
    (doc! "{it} has at least one non-deep leaf, and every \
      place reachable by walking {it} from base local {base} \
      is an owned place in body {body}")
  (body "The MIR function body." : Body)
  (base "The base local the tree is rooted at." : Local)
  (it "The initialisation tree." : InitTree)
  :=
    HasNonDeepLeaf ‹it› ∧ AllPlacesOwned ‹body, base, it›

namespace InitTree

defFn meet (.plain "meet")
  (doc! "Meet two initialisation trees, implementing the \
    recursive meet of `owned-state.md`. At matching leaves we \
    take the minimum via #InitialisationState.meet. When one \
    side is a leaf and the other is internal, the \
    uninitialised/shallow leaf dominates (its initialisation \
    state covers every descendant place), while a \
    fully-initialised leaf yields to the more precise \
    internal expansion. When both sides are `deref` nodes we \
    recurse on the child. Other internal/internal cases \
    (`fields` against `fields`, mismatched expansion shapes, \
    or `guided` expansions) conservatively collapse to \
    {Doc.m (.bold (.raw "U"))}; a faithful pointwise handling \
    of those cases is a follow-up.")
  (a "The first tree." : InitTree)
  (b "The second tree." : InitTree)
  : InitTree where
  -- Leaf + Leaf: take the minimum initialisation state.
  | .leaf x ; .leaf y =>
      .leaf ‹InitialisationState.meet ‹x, y››
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
      .internal ‹.deref ‹meet ‹a, b›››
  -- Other internal / internal combinations: conservative.
  | .internal _ ; .internal _ => .leaf ‹.uninit›

/-- The initialisation-tree meet is commutative:
    `meet a b = meet b a`. Case analysis reduces nearly every
    branch to `rfl`; the matching-leaf branch follows from
    `InitialisationState.meet_comm`, and the matching
    `.deref` branch reduces by structural recursion. -/
theorem meet_comm
    : ∀ (a b : InitTree), meet a b = meet b a
  | .leaf x, .leaf y => by
      simp only [meet, InitialisationState.meet_comm]
  | .leaf .uninit, .internal _ => rfl
  | .internal _, .leaf .uninit => rfl
  | .leaf .shallow, .internal _ => rfl
  | .internal _, .leaf .shallow => rfl
  | .leaf .deep, .internal _ => rfl
  | .internal _, .leaf .deep => rfl
  | .internal (.deref a), .internal (.deref b) => by
      simp only [meet, meet_comm a b]
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
