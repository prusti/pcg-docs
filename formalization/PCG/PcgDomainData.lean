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
    .math (.seq [.text "pdd", .sym .setContains, .text "PcgDomainData"]),
    .plain " is the dataflow record carried by the PCG \
     analysis at each basic block: a ",
    Doc.refLinkOf @DomainData "DomainData",
    .plain " whose payload at every program point is a ",
    Doc.refLinkOf @PcgData "PcgData", .plain " over MIR places."])
  := DomainData (PcgData Place)
