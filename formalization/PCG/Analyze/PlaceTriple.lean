import Core.Dsl.DefStruct
import MIR.Place
import PCG.Capability

defStruct PlaceTriple
    (.text "pt", .text "PlaceTriple")
  "Place Triples"
  (doc! "A place triple \
    {.math (.seq [(.text "pt"), .sym .setContains, (.text "PlaceTriple")])} \
    bundles a place with the capability required for the \
    place before a statement executes and the optional \
    capability established for the place after the statement \
    executes. A `None` post indicates that the statement \
    does not establish a post-condition capability on the \
    place.")
  display
    (.sym .lbrace, #pre, .sym .rbrace, .sym .space,
    #place,
    .sym .space, .sym .lbrace, #post, .sym .rbrace)
where
  | place "The place whose capability is tracked." : Place
  | pre "The capability required on the place before the \
      statement." : Capability
      symbol (.text "pre")
  | post "The capability established on the place after the \
      statement, when one is established."
      : Option Capability
  deriving BEq, Repr, Hashable
