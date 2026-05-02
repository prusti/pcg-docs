import Core.Dsl.DefEnum
import PCG.Owned.AbstractInitTree

defEnum MaterializedTreeLeaf
    (.text "mtl",
     .text "MaterializedTreeLeaf")
  "Materialised Tree Leaves"
  (doc! "A materialised tree leaf \
    $_mtl_ ∈ _MaterializedTreeLeaf_$ \
    occupies one leaf slot in a \
    {Doc.math (.text "MaterializedTree")}. It is either an \
    uninitialised or shallowly initialised leaf (which \
    cannot carry a materialised extension), or a fully \
    initialised leaf whose materialised extension is \
    recorded as an abstract initialisation tree with unit \
    per-leaf payloads.")
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
