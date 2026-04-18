import PCG.InitialisationState
import Core.Dsl.DefOrder
import Core.Order

defOrder InitialisationState where
  deep > shallow > uninit
