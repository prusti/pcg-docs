import Core.Dsl.DefAlias
import Core.Dsl.DefFn
import Core.Dsl.DefInductiveProperty
import Core.Dsl.DefProperty
import MIR.Body
import MIR.Ty
import PCG.Owned.AbstractInitTree
import PCG.Owned.InitialisationState

defAlias InitTree
    (.doc (.plain "it"),
     .doc (.plain "InitTree"))
  "Initialisation Trees"
  (.seq [
    .plain "An initialisation tree ",
    Doc.defMath (.doc (.plain "it"))
      (.doc (.plain "InitTree")),
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

defInductiveProperty HasNonDeepLeaf
    (.doc (.plain "h"), .doc (.plain "HasNonDeepLeaf"))
  "Has Non-Deep Leaf"
  (.plain "An initialisation tree contains at least one \
    descendant leaf whose capability is not fully \
    initialised. The structural recursion is captured by an \
    inference rule per `PlaceExpansion` variant.")
  (it "The initialisation tree." : InitTree)
where
  | leaf {cap : InitialisationState}
      from (cap ≠ .deep)
      ⊢ HasNonDeepLeaf (.leaf cap)
  | fields {fs} {x}
      from (x ∈ fs, HasNonDeepLeaf x.2.2)
      ⊢ HasNonDeepLeaf (.internal (.fields fs))
  | deref {d}
      from (HasNonDeepLeaf d)
      ⊢ HasNonDeepLeaf (.internal (.deref d))
  | guidedDowncast {v} {d}
      from (HasNonDeepLeaf d)
      ⊢ HasNonDeepLeaf (.internal (.guided (.downcast v d)))
  | guidedConstantIndex {n} {d}
      from (HasNonDeepLeaf d)
      ⊢ HasNonDeepLeaf
          (.internal (.guided (.constantIndex n d)))
  | guidedIndex {l} {d}
      from (HasNonDeepLeaf d)
      ⊢ HasNonDeepLeaf (.internal (.guided (.index l d)))
  | guidedSubslice {f} {t} {fromEnd} {d}
      from (HasNonDeepLeaf d)
      ⊢ HasNonDeepLeaf
          (.internal (.guided (.subslice f t fromEnd d)))

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
  (bodyDoc, baseDoc, itDoc) =>
    (.seq [.plain "every place reachable from ", baseDoc,
           .plain " in ", itDoc,
           .plain " is an owned place in body ", bodyDoc])
  (body "The MIR function body." : Body)
  (base "The base local the tree is rooted at." : Local)
  (it "The initialisation tree." : InitTree)
  :=
    places ‹it, base› ·forAll fun p =>
      placeIsOwnedIn ‹body, p›

defProperty ValidInitTree (.plain "ValidInitTree")
  (bodyDoc, baseDoc, itDoc) =>
    (.seq [itDoc, .plain " is a valid initialisation tree \
           rooted at ", baseDoc, .plain " in body ", bodyDoc])
  (body "The MIR function body." : Body)
  (base "The base local the tree is rooted at." : Local)
  (it "The initialisation tree." : InitTree)
  :=
    HasNonDeepLeaf ‹it› ∧ AllPlacesOwned ‹body, base, it›
