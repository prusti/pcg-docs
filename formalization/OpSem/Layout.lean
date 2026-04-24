import Core.Dsl.DefFn
import MIR.Ty
import OpSem.Pointer

namespace Ty

defFn layout (.plain "layout")
  (.seq [.plain "Compute the layout strategy for a MIR type, \
    following MiniRust's ", .code "Type::layout",
    .plain " stripped of alignment and trait-object handling. \
    Pointers (",
    .code "ref", .plain " and ", .code "box",
    .plain ") are assumed to be thin and use 8 bytes; the \
    unsized cases (", .code "slice", .plain ", ",
    .code "tuple", .plain ") of ", .code "LayoutStrategy",
    .plain " are not produced. Returns ", .code "None",
    .plain " for type parameters, alias types, and constructor \
    applications, whose layout cannot be determined without \
    further context."])
  (τ "The MIR type." : Ty)
  : Option LayoutStrategy where
  | .bool => Some LayoutStrategy.sized‹1›
  | .int it => Some LayoutStrategy.sized‹sizeBytes ‹it↦size››
  | .ref _ _ _ => Some LayoutStrategy.sized‹8›
  | .box _ => Some LayoutStrategy.sized‹8›
  | .array elem n =>
      let inner ← layout ‹elem› ;
      match inner with
      | .sized sz => Some LayoutStrategy.sized‹sz * n›
      | _ => None
      end
  | .param _ => None
  | .alias _ _ _ => None
  | .ctor _ _ => None

end Ty
