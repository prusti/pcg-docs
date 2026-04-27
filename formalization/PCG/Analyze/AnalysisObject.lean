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
