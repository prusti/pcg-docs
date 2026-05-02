import Core.Dsl.DefFn
import MIR.Body
import PCG.Analyze.AnalysisObject
import PCG.Analyze.PlaceTriple
import PCG.EvalStmtPhase
import PCG.Obtain.PcgData
import PCG.PcgData
import PCG.PcgDomainData

-- ══════════════════════════════════════════════
-- Stepping the PCG across a single statement phase
-- ══════════════════════════════════════════════

namespace PcgData

defFn obtainTriples (.plain "obtainTriples")
  (.plain "Apply obtain for each triple's pre-condition \
   capability in turn, threading the resulting PCG data \
   through. Returns None as soon as any obtain fails. The \
   precondition that every triple's place is valid in the \
   body discharges the corresponding precondition of obtain \
   at each step.")
  (pd "The incoming PCG data." : PcgData Place)
  (body "The function body." : Body)
  (triples "The triples whose pre-conditions to obtain."
      : List PlaceTriple)
  requires triples·forAll fun t => validPlace ‹body, t↦place›
  : Option (PcgData Place) where
  | pd ; _ ; [] => Some pd
  | pd ; body ; t :: rest =>
      let pd' ← obtain ‹pd, body, t↦place, t↦pre,
        proof[h_pre0 t (List.mem_cons_self ..)]› ;
      obtainTriples ‹pd', body, rest›

defFn analyze (.plain "analyze")
  (doc! "Step the PCG state across a single statement evaluation phase. First looks up the analysis \
    object at `loc` in `body`. For `PreOperands` the pre-conditions of every #operandTriples entry \
    are obtained on the PCG; for `PreMain` the pre-conditions of every #mainTriples entry are \
    obtained. The two `Post` phases leave the PCG unchanged.")
  (pd "The incoming PCG data." : PcgData Place)
  (body "The function body." : Body)
  (loc "The program point at which the phase is evaluated."
      : Location)
  (phase "The evaluation phase." : EvalStmtPhase)
  requires validAnalysisObject ‹body,
             getAnalysisObject ‹body, loc››
  : Option (PcgData Place) :=
    let ao := getAnalysisObject ‹body, loc› ;
    let triples :=
      match phase with
        | .preOperands => operandTriples ‹ao›
        | .preMain => mainTriples ‹ao›
        | .postOperands => ∅
        | .postMain => ∅
      end ;
    -- Discharging the `validPlace` precondition of
    -- `obtainTriples` requires showing that the `place` field
    -- of every triple in `operandTriples ao` /
    -- `mainTriples ao` is in `s.statementPlaces` (resp.
    -- `t.terminatorPlaces`) — at which point
    -- `validAnalysisObject` (which unfolds to
    -- `validStatement` / `validTerminator` and so to
    -- `forAll p ∈ statementPlaces, validPlace body p`)
    -- discharges it. That structural inclusion proof is out
    -- of scope here; leaving an explicit `sorry` at the call
    -- site documents the gap locally rather than burying it
    -- inside `obtainTriples`.
    obtainTriples ‹pd, body, triples·toList,
      proof[sorry]›

defFn analyzeAt (.plain "analyzeAt")
  (doc! "Step the PCG state across all four evaluation phases at a single location, threading each \
    phase's output into the next. The returned #PcgDomainData carries the incoming PCG data as its \
    entry state and the four per-phase states produced by `analyze`. Returns `None` if any phase \
    fails.")
  (pd "The incoming PCG data, at the entry to the location."
      : PcgData Place)
  (body "The function body." : Body)
  (loc "The location at which to step (statement or \
       terminator)." : Location)
  : Option PcgDomainData :=
    let preOp ← analyze ‹pd, body, loc, .preOperands,
      proof[sorry]› ;
    let postOp ← analyze ‹preOp, body, loc, .postOperands,
      proof[sorry]› ;
    let preM ← analyze ‹postOp, body, loc, .preMain,
      proof[sorry]› ;
    let postM ← analyze ‹preM, body, loc, .postMain,
      proof[sorry]› ;
    Some DomainData⟨pd,
      EvalStmtData⟨preOp, postOp, preM, postM⟩⟩

defFn analyzeStmtsFrom (.plain "analyzeStmtsFrom")
  (doc! "Recursively step the PCG through the remaining statements of a basic block starting at \
    `idx`, followed by the basic block's terminator. Each step calls `analyzeAt` at `Location⟨bb, \
    idx⟩`, threading the post-main state into the next step. The empty-list case is the terminator \
    step at `stmtIdx == statements.length`. Returns the per-step #PcgDomainData values, or `None` if \
    any phase fails.")
  (pd "The PCG data on entry to the next step."
      : PcgData Place)
  (body "The function body." : Body)
  (bb "The basic block being analyzed." : BasicBlockIdx)
  (idx "The current statement index within the block."
      : Nat)
  (remaining "The statements that still need to be \
       processed, in order." : List Statement)
  : Option (List PcgDomainData) :=
    match remaining with
      | [] =>
          let dd ← analyzeAt ‹pd, body, Location⟨bb, idx⟩› ;
          Some [dd]
      | _ :: rest =>
          let dd ← analyzeAt ‹pd, body, Location⟨bb, idx⟩› ;
          let restDDs ← analyzeStmtsFrom
            ‹dd↦states↦postMain, body, bb, idx + 1, rest› ;
          Some (dd :: restDDs)
    end

defFn analyzeBlock (.plain "analyzeBlock")
  (.seq [
    .plain "Step the PCG state across an entire basic \
     block: one ", .code "analyzeAt",
    .plain " call per statement followed by one for the \
     terminator. Returns the resulting list of ",
    Doc.refLinkOf @PcgDomainData "PcgDomainData", .plain " values of length ",
    .math (.bold (.raw "n+1")),
    .plain ", where ", .math (.bold (.raw "n")),
    .plain " is the statement count, or ", .code "None",
    .plain " if any phase fails."])
  (pd "The PCG data on entry to the basic block."
      : PcgData Place)
  (body "The function body." : Body)
  (bb "The basic block to analyze." : BasicBlockIdx)
  : Option (List PcgDomainData) :=
    let block := body↦blocks ! bb↦index ;
    analyzeStmtsFrom ‹pd, body, bb, 0, block↦statements›

end PcgData
