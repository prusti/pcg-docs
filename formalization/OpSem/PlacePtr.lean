import OpSem.Pointer

defStruct PlacePtr (.raw "pp",
    .text "PlacePtr")
  "Place Pointers"
  (.plain "A place pointer: a thin pointer into memory designating a place.")
where
  | ptr "The pointer." : ThinPointer
  deriving Repr, Hashable
