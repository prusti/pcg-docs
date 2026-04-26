import Core.Dsl.DefFn
import MIR.Body
import PCG.EvalStmtPhase
import PCG.PcgData

-- ══════════════════════════════════════════════
-- Stepping the PCG across a single statement phase
-- ══════════════════════════════════════════════

namespace PcgData

defFn analyze (.plain "analyze")
  (.seq [
    .plain "Step the PCG state across a single statement \
     evaluation phase at ", .code "loc",
    .plain " in ", .code "body",
    .plain ". Pattern-matches on ", .code "phase",
    .plain " so each of the four phases (",
    .code "PreOperands", .plain ", ", .code "PostOperands",
    .plain ", ", .code "PreMain", .plain ", ",
    .code "PostMain",
    .plain ") gets its own update rule. Every arm currently \
     returns the incoming ", .code "PcgData",
    .plain " unchanged — the precise per-phase logic is a \
     follow-up."])
  (pd "The incoming PCG data." : PcgData Place)
  (body "The function body." : Body)
  (loc "The program point at which the phase is evaluated."
      : Location)
  (phase "The evaluation phase." : EvalStmtPhase)
  : PcgData Place where
  | pd ; _ ; _ ; .preOperands => pd
  | pd ; _ ; _ ; .postOperands => pd
  | pd ; _ ; _ ; .preMain => pd
  | pd ; _ ; _ ; .postMain => pd

end PcgData
