import Core.Dsl.DefFn
import MIR.Body
import PCG.AnalysisObject
import PCG.Analyze.PlaceTriple
import PCG.Capability

defFn operandTriple (.plain "operandTriple")
  (doc! "The set of place triples implied by a single \
    operand: a `copy` yields a $__R__$ triple with no \
    post-condition; a `move` yields an $__E__$ triple with \
    post $__W__$; a constant contributes nothing.")
  (o "The operand." : Operand)
  : Set PlaceTriple where
  | .copy p =>
      ⦃PlaceTriple⟨p, Capability.read, None⟩⦄
  | .move p =>
      ⦃PlaceTriple⟨p, Capability.exclusive, Some Capability.write⟩⦄
  | .const _ => ∅

defFn borrowTriple (.plain "borrowTriple")
  (doc! "The place triple implied by a borrow of a place at \
    the given mutability: shared yields a $__R__$ triple with \
    no post-condition, mutable yields an $__E__$ triple with \
    post {Doc.m (.sym .emptySet)}.")
  (m "The borrow's mutability." : Mutability)
  (p "The borrowed place." : Place)
  : PlaceTriple where
  | .shared ; p =>
      PlaceTriple⟨p, Capability.read, None⟩
  | .mutable ; p =>
      PlaceTriple⟨p, Capability.exclusive, Some Capability.none⟩

defFn rvalueTriples (.plain "rvalueTriples")
  (.plain "The set of place triples implied by an rvalue: a \
   use contributes its operand's triple; a borrow \
   contributes the borrow's triple.")
  (rv "The rvalue." : Rvalue)
  : Set PlaceTriple where
  | .use o => operandTriple o
  | .ref _ m p => ⦃borrowTriple m p⦄

defFn statementTriples (.plain "statementTriples")
  (.plain "The set of place triples implied by a statement: \
   an assignment contributes its rvalue's triples; storage \
   markers contribute nothing.")
  (s "The statement." : Statement)
  : Set PlaceTriple where
  | .assign _ rhs => rvalueTriples rhs
  | .storageLive _ => ∅
  | .storageDead _ => ∅

defFn terminatorTriples (.plain "terminatorTriples")
  (.plain "The set of place triples implied by a terminator: \
   only operand-bearing variants contribute.")
  (t "The terminator." : Terminator)
  : Set PlaceTriple where
  | .goto _ => ∅
  | .switchInt o _ _ => operandTriple o
  | .return_ => ∅
  | .unreachable => ∅
  | .drop _ _ => ∅
  | .call callee args _ _ =>
      operandTriple callee ∪
        (args·setFlatMap fun a => operandTriple a)

defFn operandTriples (.plain "operandTriples")
  (doc! "The set of place triples implied by the operand and \
    borrow uses of places in an analysis object. A `copy` \
    operand or shared borrow yields a $__R__$ triple with no \
    post-condition; a `move` operand yields an $__E__$ triple \
    with post $__W__$; a mutable borrow yields an $__E__$ \
    triple with post {Doc.m (.sym .emptySet)}.")
  (ao "The analysis object." : AnalysisObject)
  : Set PlaceTriple where
  | .stmt s => statementTriples s
  | .terminator t => terminatorTriples t

defFn mainTriples (.plain "mainTriples")
  (doc! "The set of place triples implied by the main effect \
    of an analysis object. An assignment requires $__W__$ on \
    its destination and establishes $__E__$; `StorageLive` \
    transitions the local from {Doc.m (.sym .emptySet)} to \
    $__E__$; `StorageDead` transitions it from $__E__$ back \
    to {Doc.m (.sym .emptySet)}; a `drop` consumes $__E__$ \
    and leaves {Doc.m (.sym .emptySet)}; a `call` requires \
    $__W__$ on its destination and establishes $__E__$; other \
    terminators contribute nothing.")
  (ao "The analysis object." : AnalysisObject)
  : Set PlaceTriple where
  | .stmt (.assign lhs _) =>
      ⦃PlaceTriple⟨lhs, Capability.write,
        Some Capability.exclusive⟩⦄
  | .stmt (.storageLive lcl) =>
      ⦃PlaceTriple⟨Place⟨lcl, []⟩, Capability.none,
        Some Capability.exclusive⟩⦄
  | .stmt (.storageDead lcl) =>
      ⦃PlaceTriple⟨Place⟨lcl, []⟩, Capability.exclusive,
        Some Capability.none⟩⦄
  | .terminator (.drop p _) =>
      ⦃PlaceTriple⟨p, Capability.exclusive,
        Some Capability.none⟩⦄
  | .terminator (.call _ _ dest _) =>
      ⦃PlaceTriple⟨dest, Capability.write,
        Some Capability.exclusive⟩⦄
  | .terminator _ => ∅

/-- Local `Inhabited` instances scoped to this module so that
    the `[i]!` indexing inside `getAnalysisObject` elaborates
    against the source `defStruct`/`defEnum`s, which only derive
    `Repr, BEq, Hashable`. The Lean exporter adds `Inhabited`
    automatically to the corresponding generated declarations,
    so these instances are not re-emitted there. -/
private instance : Inhabited Terminator := ⟨.unreachable⟩
private instance : Inhabited Statement := ⟨.storageLive ⟨0⟩⟩
private instance : Inhabited BasicBlock := ⟨⟨[], .unreachable⟩⟩

defFn getAnalysisObject (.plain "getAnalysisObject")
  (.plain "Look up the analysis object at a location in a body: \
   the statement at the given index when one exists at that \
   position, otherwise the basic block's terminator.")
  (body "The function body." : Body)
  (loc "The location." : Location)
  requires validBody body
  ensures validAnalysisObject(body, result)
  : AnalysisObject :=
    let bb := body↦blocks ! loc↦block↦index ;
    if loc↦stmtIdx < bb↦statements·length then
      .stmt (bb↦statements ! loc↦stmtIdx)
    else
      .terminator bb↦terminator
