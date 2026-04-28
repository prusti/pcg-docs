import Core.Dsl.DefAlias
import MIR.Place
import PCG.DomainData
import PCG.PcgData

defAlias PcgDomainData
    (.text "pdd",
     .text "PcgDomainData")
  "PCG Domain Data"
  (.seq [
    .plain "PCG domain data ",
    Doc.defMath (.text "pdd")
      (.text "PcgDomainData"),
    .plain " is the dataflow record carried by the PCG \
     analysis at each basic block: a ",
    .code "DomainData",
    .plain " whose payload at every program point is a ",
    .code "PcgData", .plain " over MIR places."])
  := DomainData (PcgData Place)
