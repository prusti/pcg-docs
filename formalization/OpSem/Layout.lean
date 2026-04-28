import Core.Dsl.DefFn
import Core.Dsl.DefProperty
import MIR.Ty
import OpSem.Pointer

defProperty IsSized (.plain "IsSized")
  short (τDoc) =>
    (.seq [τDoc, .plain " is a sized type"])
  long (τDoc) =>
    (.seq [τDoc, .plain " is a primitive (",
           .code "bool", .plain ", ", .code "int",
           .plain "), a pointer (", .code "ref",
           .plain ", ", .code "box", .plain "), or an \
           array of a sized element"])
  (τ "The MIR type." : Ty)
  where
  | .bool => true
  | .int _ => true
  | .ref _ _ _ => true
  | .box _ => true
  | .array elem _ => IsSized ‹elem›
  | _ => false

namespace Ty

defFn sizeOf (.plain "sizeOf")
  (.seq [.plain "Compute the byte size of a sized MIR type. \
    Pointers (", .code "ref", .plain " and ", .code "box",
    .plain ") are assumed to be thin and use 8 bytes; \
    arrays scale their element's size by the array length. \
    The ", .code "IsSized",
    .plain " precondition rules out the type-parameter, \
    alias, and constructor-application cases (whose size \
    cannot be determined without further context) and \
    rules out array elements that are themselves not sized."])
  (τ "The MIR type." : Ty)
  requires IsSized(τ)
  : Nat where
  | .bool => 1
  | .int it => sizeBytes ‹it↦size›
  | .ref _ _ _ => 8
  | .box _ => 8
  | .array elem n => sizeOf ‹elem› * n

defFn layout (.plain "layout")
  (.seq [.plain "Compute the layout strategy of a sized MIR \
    type, following MiniRust's ", .code "Type::layout",
    .plain " stripped of alignment and trait-object \
    handling: every sized type lays out as a single ",
    .code "LayoutStrategy.sized",
    .plain " bucket whose width is given by ", .code "sizeOf",
    .plain "."])
  (τ "The MIR type." : Ty)
  requires IsSized(τ)
  : LayoutStrategy :=
    LayoutStrategy.sized
      ‹sizeOf ‹τ, lean_proof("h_IsSized")››

end Ty
