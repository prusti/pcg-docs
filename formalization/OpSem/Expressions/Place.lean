import OpSem.Machine
import OpSem.PlacePtr

namespace Machine

defFn evalLocal (.plain "evalLocal")
  (.seq [.plain "Evaluate a local variable, returning its \
    place pointer. Returns ", .code "None",
    .plain " if the local is dead."])
  (machine "The machine state." : Machine)
  (lcl "The local variable." : Local)
  requires Runnable(machine)
  : Option PlacePtr :=
    let frame := currentFrame
      ‹machine, lean_proof("h_Runnable")› ;
    let ptr ← mapGet ‹frame↦locals, lcl› ;
    Some PlacePtr⟨ptr⟩

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
  (.seq [.plain "Evaluate a field projection on a place \
    pointer. Given the place, field index, and the \
    container type, computes the byte offset and \
    returns the field's place pointer and type. \
    Returns ", .code "None",
    .plain " if the type is not a constructor type, \
    the field index is out of bounds, or the offset \
    cannot be computed."])
  (place "The place pointer of the container." : PlacePtr)
  (field "The field index." : FieldIdx)
  (ty "The type of the container." : Ty)
  : Option (PlacePtr × Ty) where
  | place ; field ; .ctor _ args =>
      let fieldTy := args ! field↦index ;
      let offset ← fieldOffset ‹args, field↦index› ;
      Some ⟨PlacePtr⟨ThinPointer⟨place↦ptr↦addr + offset, place↦ptr↦provenance⟩⟩, fieldTy⟩
  | _ ; _ ; _ => None

defFn evalProjs (.plain "evalProjs")
  (.seq [.plain "Evaluate a sequence of projection \
    elements, threading a place pointer and type \
    through each step. ", .code ".field",
    .plain " advances the place by the field's byte offset \
    and updates the type to the field's type; ",
    .code ".downcast",
    .plain " is a no-op on the place pointer — variant \
    selection only affects subsequent typed access, not \
    the address itself. ", .code ".deref", .plain " and ",
    .code ".index",
    .plain " need to load values out of memory and are not \
    yet handled here (they fall through to ", .code "None",
    .plain ")."])
  (place "The current place pointer." : PlacePtr)
  (ty "The current type." : Ty)
  (projs "The remaining projections." : List ProjElem)
  : Option (PlacePtr × Ty) where
  | place ; ty ; [] => Some ⟨place, ty⟩
  | place ; ty ; (.field idx _) :: rest =>
      let ⟨fp, ft⟩ ← evalField ‹place, idx, ty› ;
      evalProjs ‹fp, ft, rest›
  | place ; ty ; (.downcast _) :: rest =>
      evalProjs ‹place, ty, rest›
  | _ ; _ ; _ :: _ => None

defFn evalPlace (.plain "evalPlace")
  (.seq [.plain "Evaluate a place to a place pointer \
    and its type. Looks up the base local with ",
    .code "evalLocal", .plain ", then applies each \
    projection element with ", .code "evalProjs",
    .plain "."])
  (machine "The machine state." : Machine)
  (place "The place to evaluate." : Place)
  requires Runnable(machine)
  : Option (PlacePtr × Ty) :=
    let frame := currentFrame
      ‹machine, lean_proof("h_Runnable")› ;
    let rootPlace ← evalLocal
      ‹machine, place↦«local», lean_proof("h_Runnable")› ;
    let rootTy := frame↦body↦decls ! place↦«local»↦index ;
    evalProjs ‹rootPlace, rootTy, place↦projection›

end Machine
