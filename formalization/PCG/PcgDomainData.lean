import Core.Dsl.DefAlias
import MIR.Place
import PCG.DomainData
import PCG.PcgData

defAlias PcgDomainData
    (.doc (.plain "pdd"),
     .doc (.plain "PcgDomainData"))
  "PCG Domain Data"
  (.seq [
    .plain "PCG domain data ",
    Doc.defMath (.doc (.plain "pdd"))
      (.doc (.plain "PcgDomainData")),
    .plain " is the dataflow record carried by the PCG \
     analysis at each basic block: a ",
    .code "DomainData",
    .plain " whose payload at every program point is a ",
    .code "PcgData", .plain " over MIR places."])
  := DomainData (PcgData Place)
