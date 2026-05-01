import Core.Dsl.DefFn
import MIR.IsSized
import MIR.Ty
import OpSem.Pointer

namespace Ty

defFn sizeOf (.plain "sizeOf")
  (doc! "Compute the byte size of a sized MIR type. Pointers (`ref` and `box`) are assumed to be \
    thin and use 8 bytes; arrays scale their element's size by the array length. The #IsSized \
    precondition rules out the type-parameter, alias, and constructor-application cases (whose size \
    cannot be determined without further context) and rules out array elements that are themselves \
    not sized.")
  (τ "The MIR type." : Ty)
  requires IsSized(τ)
  : Nat where
  | .bool => 1
  | .int it => sizeBytes ‹it↦size›
  | .ref _ _ _ => 8
  | .box _ => 8
  | .array elem n => sizeOf ‹elem› * n

defFn layout (.plain "layout")
  (doc! "Compute the layout strategy of a sized MIR type, following MiniRust's `Type::layout` \
    stripped of alignment and trait-object handling: every sized type lays out as a single \
    #LayoutStrategy.sized bucket whose width is given by `sizeOf`.")
  (τ "The MIR type." : Ty)
  requires IsSized(τ)
  : LayoutStrategy :=
    LayoutStrategy.sized
      ‹sizeOf ‹τ, lean_proof("h_IsSized")››

end Ty
