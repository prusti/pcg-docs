import Core.Dsl.DefFn
import MIR.Body
import PCG.Analyze.AnalysisObject
import PCG.Analyze.PlaceTriple
import PCG.EvalStmtPhase
import PCG.Obtain.PcgData
import PCG.PcgData

-- ══════════════════════════════════════════════
-- Stepping the PCG across a single statement phase
-- ══════════════════════════════════════════════

namespace PcgData

defFn obtainTriples (.plain "obtainTriples")
  (.plain "Apply obtain for each triple's pre-condition \
   capability in turn, threading the resulting PCG data \
   through. Returns None as soon as any obtain fails.")
  (pd "The incoming PCG data." : PcgData Place)
  (body "The function body." : Body)
  (triples "The triples whose pre-conditions to obtain."
      : List PlaceTriple)
  : Option (PcgData Place) where
  | pd ; _ ; [] => Some pd
  | pd ; body ; t :: rest =>
      let pd' ← obtain ‹pd, body, t↦place, t↦pre,
        lean_proof("sorry")› ;
      obtainTriples ‹pd', body, rest›

defFn analyze (.plain "analyze")
  (.seq [
    .plain "Step the PCG state across a single statement \
     evaluation phase. First looks up the analysis object \
     at ", .code "loc", .plain " in ", .code "body",
    .plain ". For ", .code "PreOperands", .plain " the \
     pre-conditions of every ", .code "operandTriples",
    .plain " entry are obtained on the PCG; for ",
    .code "PreMain", .plain " the pre-conditions of every ",
    .code "mainTriples", .plain " entry are obtained. The \
     two ", .code "Post", .plain " phases leave the PCG \
     unchanged."])
  (pd "The incoming PCG data." : PcgData Place)
  (body "The function body." : Body)
  (loc "The program point at which the phase is evaluated."
      : Location)
  (phase "The evaluation phase." : EvalStmtPhase)
  : Option (PcgData Place) :=
    let ao := getAnalysisObject ‹body, loc› ;
    let triples :=
      match phase with
        | .preOperands => operandTriples ‹ao›
        | .preMain => mainTriples ‹ao›
        | .postOperands => ∅
        | .postMain => ∅
      end ;
    obtainTriples ‹pd, body, triples·toList›

end PcgData
