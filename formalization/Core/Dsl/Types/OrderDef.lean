
/-- A covering relation in a partial order: `greater > lesser`. -/
structure OrderFact where
  greater : String
  lesser : String
  deriving Repr

/-- Metadata for an ordering on a finite enum, used for
    cross-language export and presentation. -/
structure OrderDef where
  /-- The enum type name. -/
  enumName : String
  /-- Variant names (in declaration order). -/
  elements : List String
  /-- The covering relations (Hasse diagram edges). -/
  facts : List OrderFact
  /-- Full reflexive-transitive closure as `(a, b)` where `a ≤ b`. -/
  closure : List (String × String)
  deriving Repr

