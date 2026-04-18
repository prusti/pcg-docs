import PCG.Capability
import Core.Dsl.DefOrder
import Core.Order

defOrder Capability where
  | exclusive > read
  | exclusive > shallowExclusive
  | shallowExclusive > write
  | write > none
  | read > none
