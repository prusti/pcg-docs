import OpSem.Machine
import OpSem.PlacePtr

namespace Machine

defFn evalLocal (.plain "evalLocal")
  (doc! "Evaluate a local variable, returning its place pointer. Returns `None` if the local is \
    dead.")
  (machine "The machine state." : Machine)
  (lcl "The local variable." : Local)
  requires Runnable(machine)
  : Option PlacePtr :=
    let frame := currentFrame
      ‹machine, proof[h_Runnable]› ;
    let ptr ← mapGet ‹frame↦locals, lcl› ;
    Some PlacePtr⟨ptr⟩

defFn fieldOffset (.plain "fieldOffset")
  (doc! "Compute the byte offset of a field at position `idx` within a list of field types. Returns \
    `None` if any preceding field has unknown size or the index is out of bounds.")
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
  (doc! "Evaluate a field projection on a place pointer. Given the place, field index, and the \
    container type, computes the byte offset and returns the field's place pointer and type. Returns \
    `None` if the type is not a constructor type, the field index is out of bounds, or the offset \
    cannot be computed.")
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
    selection only affects subsequent typed access. ",
    .code ".deref",
    .plain " loads the pointer stored at the current place \
    via ", Doc.refLinkOf @decodePtr "decodePtr",
    .plain " and continues evaluation at the loaded \
    pointer's address (the new type is the pointee). ",
    .code ".index",
    .plain " loads the index local's value and advances the \
     address by ", .code "index * elemSize", .plain "."])
  (m "The machine state." : Machine)
  (place "The current place pointer." : PlacePtr)
  (ty "The current type." : Ty)
  (projs "The remaining projections." : List ProjElem)
  requires Runnable(m)
  : Option (PlacePtr × Ty) where
  | _ ; place ; ty ; [] => Some ⟨place, ty⟩
  | m ; place ; ty ; (.field idx _) :: rest =>
      let ⟨fp, ft⟩ ← evalField ‹place, idx, ty› ;
      evalProjs ‹m, fp, ft, rest›
  | m ; place ; ty ; (.downcast _) :: rest =>
      evalProjs ‹m, place, ty, rest›
  | m ; place ; .ref _ _ pointee ; .deref :: rest =>
      let bytes := Memory.load ‹m↦mem, place↦ptr, 8› ;
      let ptr ← decodePtr ‹bytes› ;
      evalProjs ‹m, PlacePtr⟨ptr⟩, pointee, rest›
  | m ; place ; .box pointee ; .deref :: rest =>
      let bytes := Memory.load ‹m↦mem, place↦ptr, 8› ;
      let ptr ← decodePtr ‹bytes› ;
      evalProjs ‹m, PlacePtr⟨ptr⟩, pointee, rest›
  | m ; place ; .array elem _ ; (.index lcl) :: rest =>
      let elemSz ← Ty.bytes ‹elem› ;
      let idxPp ← evalLocal
        ‹m, lcl, proof[h_Runnable]› ;
      let idxBytes := Memory.load ‹m↦mem, idxPp↦ptr, 8› ;
      let idxRaw ← data ‹idxBytes› ;
      let off := decodeLeUnsigned ‹idxRaw› * elemSz ;
      let newPtr := ThinPointer⟨
        Address⟨place↦ptr↦addr↦addr + off⟩,
        place↦ptr↦provenance⟩ ;
      evalProjs ‹m, PlacePtr⟨newPtr⟩, elem, rest›
  | _ ; _ ; _ ; _ :: _ => None

defFn evalPlace (.plain "evalPlace")
  (doc! "Evaluate a place to a place pointer and its type. Looks up the base local with \
    `evalLocal`, then applies each projection element with `evalProjs`.")
  (machine "The machine state." : Machine)
  (place "The place to evaluate." : Place)
  requires Runnable(machine)
  : Option (PlacePtr × Ty) :=
    let frame := currentFrame
      ‹machine, proof[h_Runnable]› ;
    let rootPlace ← evalLocal
      ‹machine, place↦«local», proof[h_Runnable]› ;
    let rootTy := frame↦body↦decls ! place↦«local»↦index ;
    evalProjs ‹machine, rootPlace, rootTy, place↦projection,
               proof[h_Runnable]›

end Machine
