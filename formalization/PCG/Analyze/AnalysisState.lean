import Core.Dsl.DefProperty
import Core.Dsl.DefStruct
import MIR.Body
import PCG.Analyze.AnalysisResults
import PCG.PcgData
import PCG.PcgDomainData

defStruct AnalysisState
    (.text "as",
     .text "AnalysisState")
  "Per-body Analysis State"
  (doc! "An analysis state \
    $_as_ ∈ _AnalysisState_$ \
    bundles the in-progress per-block analysis results with \
    the entry-state map populated by forward propagation. \
    When a block `bb` is processed, its result is recorded \
    in `results` and its post-main exit state is joined \
    into `entryStates` for every successor of `bb`. \
    Successor entries that have not yet received a \
    contribution simply become that contribution; \
    subsequent contributions are folded in via \
    `PcgData.join`.")
where
  | results "Per-block analysis results recorded so far."
      : AnalysisResults
  | entryStates "Pending entry state for each block, joined \
       from already-processed predecessors."
      : Map BasicBlockIdx (PcgData Place)
  deriving Repr

defProperty validAnalysisState (.plain "validAnalysisState")
  short
    (doc! "{state} is a valid analysis state for {body}")
  long
    (doc! "the per-block analysis results of {state} are \
      valid against {body}, and every pending entry-state \
      #PcgData in {state}'s `entryStates` map is a valid \
      PCG data for {body}")
  (body "The function body." : Body)
  (state "The analysis state." : AnalysisState)
  :=
    validAnalysisResults body state↦results ∧
    mapValues state↦entryStates·forAll fun pcg =>
      validPcgData body pcg
