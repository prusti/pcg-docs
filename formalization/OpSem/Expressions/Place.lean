import OpSem.Machine
import OpSem.RuntimePlace

namespace Machine

defFn evalLocal (.plain "evalLocal")
  (.seq [.plain "Evaluate a local variable, returning its \
    runtime place. Returns ", .code "None",
    .plain " if the thread's stack is empty or the local \
    is dead."])
  (machine "The machine state." : Machine)
  (lcl "The local variable." : Local)
  : Option RuntimePlace :=
    let frame ← currentFrame ‹machine› ;
    let ptr ← mapGet ‹frame↦locals, lcl› ;
    Some RuntimePlace⟨ptr⟩

defFn fieldOffset (.plain "fieldOffset")
  (.seq [.plain "Compute the byte offset of a field at \
    position ", .code "idx",
    .plain " within a list of field types. Returns ",
    .code "None",
    .plain " if any preceding field has unknown size \
    or the index is out of bounds."])
  (fields "The field types." : List Ty)
  (idx "The target field index." : Nat)
  : Option Nat where
  | [] ; _ => None
  | (_ :: _) ; 0 => Some 0
  | (ty :: rest) ; idx =>
      let sz ← Ty.bytes ‹ty› ;
      let off ← fieldOffset ‹rest, idx - 1› ;
      Some (sz + off)

defFn evalField (.plain "evalField")
  (.seq [.plain "Evaluate a field projection on a runtime \
    place. Given the place, field index, and the \
    container type, computes the byte offset and \
    returns the field's runtime place and type. \
    Returns ", .code "None",
    .plain " if the type is not a constructor type, \
    the field index is out of bounds, or the offset \
    cannot be computed."])
  (place "The runtime place of the container." : RuntimePlace)
  (field "The field index." : FieldIdx)
  (ty "The type of the container." : Ty)
  : Option (RuntimePlace × Ty) where
  | place ; field ; .ctor _ args =>
      let fieldTy := args ! field↦index ;
      let offset ← fieldOffset ‹args, field↦index› ;
      Some ⟨RuntimePlace⟨ThinPointer⟨place↦ptr↦addr + offset, place↦ptr↦provenance⟩⟩, fieldTy⟩
  | _ ; _ ; _ => None

defFn evalProjs (.plain "evalProjs")
  (.seq [.plain "Evaluate a sequence of projection \
    elements, threading a runtime place and type \
    through each step. Currently only field \
    projections are supported."])
  (place "The current runtime place." : RuntimePlace)
  (ty "The current type." : Ty)
  (projs "The remaining projections." : List ProjElem)
  : Option (RuntimePlace × Ty) where
  | place ; ty ; [] => Some ⟨place, ty⟩
  | place ; ty ; (.field idx _) :: rest =>
      let ⟨fp, ft⟩ ← evalField ‹place, idx, ty› ;
      evalProjs ‹fp, ft, rest›
  | _ ; _ ; _ :: _ => None

defFn evalPlace (.plain "evalPlace")
  (.seq [.plain "Evaluate a place to a runtime place \
    and its type. Looks up the base local with ",
    .code "evalLocal", .plain ", then applies each \
    projection element with ", .code "evalProjs",
    .plain "."])
  (machine "The machine state." : Machine)
  (place "The place to evaluate." : Place)
  : Option (RuntimePlace × Ty) :=
    let frame ← currentFrame ‹machine› ;
    let rootPlace ← evalLocal ‹machine, place↦«local»› ;
    let rootTy := frame↦body↦decls ! place↦«local»↦index ;
    evalProjs ‹rootPlace, rootTy, place↦projection›

end Machine
