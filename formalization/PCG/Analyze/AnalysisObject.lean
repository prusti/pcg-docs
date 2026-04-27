import Core.Dsl.DefFn
import MIR.Body
import PCG.AnalysisObject
import PCG.Analyze.PlaceTriple
import PCG.Capability

defFn operandTriple (.plain "operandTriple")
  (.seq [
    .plain "The set of place triples implied by a single \
     operand: a ", .code "copy", .plain " yields a ",
    .math (.bold (.raw "R")),
    .plain " triple with no post-condition; a ",
    .code "move", .plain " yields an ",
    .math (.bold (.raw "E")), .plain " triple with post ",
    .math (.bold (.raw "W")),
    .plain "; a constant contributes nothing."])
  (o "The operand." : Operand)
  : Set PlaceTriple where
  | .copy p =>
      ⦃PlaceTriple⟨p, Capability.read, None⟩⦄
  | .move p =>
      ⦃PlaceTriple⟨p, Capability.exclusive, Some Capability.write⟩⦄
  | .const _ => ∅

defFn borrowTriples (.plain "borrowTriples")
  (.seq [
    .plain "The set of place triples implied by a borrow of \
     a place at the given mutability: shared yields a ",
    .math (.bold (.raw "R")),
    .plain " triple with no post-condition, mutable yields \
     an ", .math (.bold (.raw "E")), .plain " triple with \
     post ", .math (.sym .emptySet), .plain "."])
  (m "The borrow's mutability." : Mutability)
  (p "The borrowed place." : Place)
  : Set PlaceTriple where
  | .shared ; p =>
      ⦃PlaceTriple⟨p, Capability.read, None⟩⦄
  | .mutable ; p =>
      ⦃PlaceTriple⟨p, Capability.exclusive, Some Capability.none⟩⦄

defFn rvalueTriples (.plain "rvalueTriples")
  (.plain "The set of place triples implied by an rvalue: a \
   use contributes its operand's triple; a borrow \
   contributes the borrow's triple.")
  (rv "The rvalue." : Rvalue)
  : Set PlaceTriple where
  | .use o => operandTriple ‹o›
  | .ref _ m p => borrowTriples ‹m, p›

defFn statementTriples (.plain "statementTriples")
  (.plain "The set of place triples implied by a statement: \
   an assignment contributes its rvalue's triples; storage \
   markers contribute nothing.")
  (s "The statement." : Statement)
  : Set PlaceTriple where
  | .assign _ rhs => rvalueTriples ‹rhs›
  | .storageLive _ => ∅
  | .storageDead _ => ∅

defFn terminatorTriples (.plain "terminatorTriples")
  (.plain "The set of place triples implied by a terminator: \
   only operand-bearing variants contribute.")
  (t "The terminator." : Terminator)
  : Set PlaceTriple where
  | .goto _ => ∅
  | .switchInt o => operandTriple ‹o›
  | .return_ => ∅
  | .unreachable => ∅
  | .drop _ _ => ∅
  | .call callee args _ _ =>
      operandTriple ‹callee› ∪
        (args·setFlatMap fun a => operandTriple ‹a›)

defFn operandTriples (.plain "operandTriples")
  (.seq [
    .plain "The set of place triples implied by the operand \
     and borrow uses of places in an analysis object. A ",
    .code "copy", .plain " operand or shared borrow yields a ",
    .math (.bold (.raw "R")),
    .plain " triple with no post-condition; a ", .code "move",
    .plain " operand yields an ", .math (.bold (.raw "E")),
    .plain " triple with post ", .math (.bold (.raw "W")),
    .plain "; a mutable borrow yields an ",
    .math (.bold (.raw "E")), .plain " triple with post ",
    .math (.sym .emptySet), .plain "."])
  (ao "The analysis object." : AnalysisObject)
  : Set PlaceTriple where
  | .stmt s => statementTriples ‹s›
  | .terminator t => terminatorTriples ‹t›

defFn mainTriples (.plain "mainTriples")
  (.seq [
    .plain "The set of place triples implied by the main \
     effect of an analysis object. An assignment requires ",
    .math (.bold (.raw "W")),
    .plain " on its destination and establishes ",
    .math (.bold (.raw "E")),
    .plain "; ", .code "StorageLive",
    .plain " transitions the local from ",
    .math (.sym .emptySet), .plain " to ",
    .math (.bold (.raw "E")), .plain "; ", .code "StorageDead",
    .plain " transitions it from ", .math (.bold (.raw "E")),
    .plain " back to ", .math (.sym .emptySet), .plain "; a ",
    .code "drop", .plain " consumes ", .math (.bold (.raw "E")),
    .plain " and leaves ", .math (.sym .emptySet),
    .plain "; a ", .code "call",
    .plain " requires ", .math (.bold (.raw "W")),
    .plain " on its destination and establishes ",
    .math (.bold (.raw "E")),
    .plain "; other terminators contribute nothing."])
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
  : AnalysisObject :=
    let bb := body↦basicBlocks ! loc↦block↦index ;
    if loc↦stmtIdx < bb↦statements·length then
      .stmt ‹bb↦statements ! loc↦stmtIdx›
    else
      .terminator ‹bb↦terminator›
