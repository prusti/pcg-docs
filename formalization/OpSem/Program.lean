import Core.Dsl.DefFn
import Core.Dsl.DefProperty
import Core.Dsl.DefStruct
import MIR.Body

defStruct Program (.text "prog",
    .text "Program")
  "Programs"
  (.seq [
    .plain "A program ",
    Doc.defMath (.text "prog")
      (.text "Program"),
    .plain " bundles every function known to the PCG together \
     with the name of the entry point. Each function is keyed \
     by its name so calls can be resolved by looking the \
     callee's name up in the map."])
where
  | functions "The function bodies keyed by function name."
      : Map String Body
  | start "The name of the entry function." : String
  deriving Repr

defProperty validProgram (.plain "validProgram")
  short (programDoc) =>
    (.seq [programDoc, .plain " is a valid program"])
  long (programDoc) =>
    (.seq [.plain "the start function name of ", programDoc,
           .plain " is registered in the function map of ",
           programDoc])
  (program "The program." : Program)
  :=
    program↦start ∈ program↦functions

namespace Program

defFn startProgram (.plain "startProgram")
  (.seq [.plain "Look up the body of the program's start \
    function. Safe because the ", .code "validProgram",
    .plain " precondition guarantees the start name is \
    registered in the function map."])
  (program "The program." : Program)
  requires validProgram(program)
  : Body :=
    mapAt ‹program↦functions, program↦start›

end Program
