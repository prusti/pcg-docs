import Core.Dsl.DefAlias
import Core.Dsl.DefProperty
import MIR.Body
import MIR.Place
import PCG.DomainData
import PCG.PcgData

defAlias PcgDomainData
    (.text "pdd",
     .text "PcgDomainData")
  "PCG Domain Data"
  (doc! "PCG domain data \
    $_pdd_ ∈ _PcgDomainData_$ \
    is the dataflow record carried by the PCG analysis at \
    each basic block: a #DomainData whose payload at every \
    program point is a #PcgData over MIR places.")
  := DomainData (PcgData Place)

defProperty validPcgDomainData (.plain "validPcgDomainData")
  short
    (doc! "{pdd} is a valid PCG domain data for {body}")
  long
    (doc! "every #PcgData carried by {pdd} — the entry-state \
      value plus all four per-#EvalStmtPhase values — is a \
      valid PCG data for {body}")
  (body "The function body." : Body)
  (pdd "The PCG domain data." : PcgDomainData)
  :=
    validPcgData body pdd↦entryState ∧
    validPcgData body pdd↦states↦preOperands ∧
    validPcgData body pdd↦states↦postOperands ∧
    validPcgData body pdd↦states↦preMain ∧
    validPcgData body pdd↦states↦postMain
