import Core.Dsl.DefEnum
import PCG.Owned.AbstractInitTree

defEnum MaterializedTreeLeaf
    (.text "mtl",
     .text "MaterializedTreeLeaf")
  "Materialised Tree Leaves"
  (.seq [
    .plain "A materialised tree leaf ",
    .math (.seq [.text "mtl", .sym .setContains, .text "MaterializedTreeLeaf"]),
    .plain " occupies one leaf slot in a ",
    .math (.text "MaterializedTree"),
    .plain ". It is either an uninitialised or shallowly \
     initialised leaf (which cannot carry a materialised \
     extension), or a fully initialised leaf whose \
     materialised extension is recorded as an abstract \
     initialisation tree with unit per-leaf payloads."])
where
  | uninit
    "Uninitialised or moved-out."
    (.bold (.raw "U"))
  | shallow
    "Shallowly initialised."
    (.bold (.raw "S"))
  | tree (ext : AbstractInitTree Unit)
    "A fully initialised leaf together with its materialised \
     extension (trivial when the subtree is a single leaf)."
    (#ext)
  deriving Repr
