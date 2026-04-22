import Core.Dsl.DefAlias
import Core.Dsl.DefInductiveProperty
import PCG.Owned.AbstractInitTree
import PCG.Owned.InitialisationState

defAlias InitialisationTree
    (.doc (.plain "it"),
     .doc (.plain "InitialisationTree"))
  "Initialisation Trees"
  (.seq [
    .plain "An initialisation tree ",
    Doc.defMath (.doc (.plain "it"))
      (.doc (.plain "InitialisationTree")),
    .plain " describes the initialisation state of an owned \
     place: an abstract initialisation tree whose leaves each \
     carry an initialisation state. By invariant, an internal \
     node has at least one descendant leaf that is not fully \
     initialised (otherwise the subtree collapses to a single ",
    .math (.bold (.raw "D")),
    .plain " leaf)."])
  := AbstractInitTree InitialisationState

defInductiveProperty HasNonDeepLeaf
    (.doc (.plain "h"), .doc (.plain "HasNonDeepLeaf"))
  "Has Non-Deep Leaf"
  (.plain "An initialisation tree contains at least one \
    descendant leaf whose capability is not fully \
    initialised. The structural recursion is captured by an \
    inference rule per `PlaceExpansion` variant.")
  (it "The initialisation tree." : InitialisationTree)
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

defInductiveProperty ValidInitTree
    (.doc (.plain "v"), .doc (.plain "ValidInitTree"))
  "Valid Initialisation Tree"
  (.plain "Structural validity of an initialisation tree: \
    every internal subtree contains at least one descendant \
    leaf that is not fully initialised, and each child is \
    itself a valid initialisation tree.")
  (it "The initialisation tree." : InitialisationTree)
where
  | leaf {cap : InitialisationState}
      ⊢ ValidInitTree (.leaf cap)
  | fields {fs}
      from (∀ x ∈ fs, ValidInitTree x.2.2,
            HasNonDeepLeaf (.internal (.fields fs)))
      ⊢ ValidInitTree (.internal (.fields fs))
  | deref {d}
      from (ValidInitTree d, HasNonDeepLeaf d)
      ⊢ ValidInitTree (.internal (.deref d))
  | guidedDowncast {v} {d}
      from (ValidInitTree d, HasNonDeepLeaf d)
      ⊢ ValidInitTree (.internal (.guided (.downcast v d)))
  | guidedConstantIndex {n} {d}
      from (ValidInitTree d, HasNonDeepLeaf d)
      ⊢ ValidInitTree
          (.internal (.guided (.constantIndex n d)))
  | guidedIndex {l} {d}
      from (ValidInitTree d, HasNonDeepLeaf d)
      ⊢ ValidInitTree (.internal (.guided (.index l d)))
  | guidedSubslice {f} {t} {fromEnd} {d}
      from (ValidInitTree d, HasNonDeepLeaf d)
      ⊢ ValidInitTree
          (.internal (.guided (.subslice f t fromEnd d)))
