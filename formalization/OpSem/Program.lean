import Core.Dsl.DefFn
import Core.Dsl.DefProperty
import Core.Dsl.DefStruct
import MIR.Body

defStruct Program (.text "prog",
    .text "Program")
  "Programs"
  (doc! "A program $_prog_ ∈ _Program_$ \
    bundles every function known to the PCG together with the name \
    of the entry point. Each function is keyed by its name so calls \
    can be resolved by looking the callee's name up in the map.")
where
  | functions "The function bodies keyed by function name."
      : Map String Body
  | start "The name of the entry function." : String
  deriving Repr

defProperty validProgram (.plain "validProgram")
  short
    (doc! "{program} is a valid program")
  long
    (doc! "the start function name of {program} is registered \
      in the function map of {program}, and every body \
      registered in that map is itself a valid body")
  (program "The program." : Program)
  :=
    program↦start ∈ program↦functions ∧
    mapValues program↦functions·forAll fun b =>
      validBody b

namespace Program

defFn startProgram (.plain "startProgram")
  (doc! "Look up the body of the program's start function. Safe because the #validProgram \
    precondition guarantees the start name is registered in the function map.")
  (program "The program." : Program)
  requires validProgram program
  : Body :=
    mapAt program↦functions program↦start

end Program
