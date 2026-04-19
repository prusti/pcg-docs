import OpSem.Pointer

defStruct RuntimePlace (.raw "rp",
    .doc (.plain "RuntimePlace"))
  "Runtime Places"
  (.plain "A runtime place: a thin pointer into memory.")
where
  | ptr "The pointer." : ThinPointer
  deriving Repr, Hashable
