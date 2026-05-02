import Core.Dsl.DefAlias
import MIR.Place
import PCG.DomainData
import PCG.PcgData

defAlias PcgDomainData
    (.text "pdd",
     .text "PcgDomainData")
  "PCG Domain Data"
  (doc! "PCG domain data \
    {.math (.seq [(.text "pdd"), .sym .setContains, (.text "PcgDomainData")])} \
    is the dataflow record carried by the PCG analysis at \
    each basic block: a #DomainData whose payload at every \
    program point is a #PcgData over MIR places.")
  := DomainData (PcgData Place)
