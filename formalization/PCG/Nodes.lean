import Core.Dsl.Descr
import PCG.Nodes.AnalysisLocation
import PCG.Nodes.LifetimeProjection
import PCG.Nodes.LifetimeProjectionLabel
import PCG.Nodes.LocalLifetimeProjection
import PCG.Nodes.MaybeLabelledPlace
import PCG.Nodes.PcgLifetimeProjection
import PCG.Nodes.PcgLifetimeProjectionBase
import PCG.Nodes.PcgNode
import PCG.Nodes.PcgPlace
import PCG.Nodes.SnapshotLocation

descr (.plain "Place- and projection-like types that appear as \
   (or compose into) the endpoints of PCG hyperedges, together \
   with the analysis locations and snapshot-location labels \
   they depend on.")
