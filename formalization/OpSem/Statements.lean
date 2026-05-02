import OpSem.Expressions.Place
import OpSem.Machine
import OpSem.PlacePtr
import Core.Dsl.Descr

namespace Machine

descr (doc! "Based on statements as described \
  {Doc.link (.plain "here") "https://github.com/minirust/minirust/blob/master/spec/lang/step/statements.md"}")

defFn placeStore (.plain "placeStore")
  (doc! "Store a value into the location designated by a place pointer. Alignment and atomicity are \
    not currently modelled, so this simply delegates to `typedStore` using the place's thin pointer.")
  (m "The memory." : Memory)
  (place "The place to store into." : PlacePtr)
  (v "The value to store." : Value)
  : Memory :=
    typedStore m place↦ptr v

defFn placeLoad (.plain "placeLoad")
  (doc! "Load a value from the location designated by a place pointer. Alignment and atomicity are \
    not currently modelled, so this simply delegates to `typedLoad` using the place's thin pointer.")
  (m "The memory." : Memory)
  (place "The place to load from." : PlacePtr)
  (ty "The type to load." : Ty)
  : Option Value :=
    typedLoad m place↦ptr ty

defFn evalOperand (.plain "evalOperand")
  (doc! "Evaluate a MIR operand to a runtime value. `copy` and `move` resolve the operand's place \
    and load the value from memory at the resulting place pointer; `const` converts the constant \
    directly via `evalConstant`. Move semantics (storage invalidation of the source) are not yet \
    modelled — both `copy` and `move` currently just load.")
  (m "The machine state." : Machine)
  (o "The operand." : Operand)
  requires Runnable m
  : Option Value where
  | m ; .copy p =>
      let ⟨pp, ty⟩ ←
        evalPlace m p proof[h_Runnable] ;
      placeLoad m↦mem pp ty
  | m ; .move p =>
      let ⟨pp, ty⟩ ←
        evalPlace m p proof[h_Runnable] ;
      placeLoad m↦mem pp ty
  | _ ; .const cv => Some (evalConstant cv)

defFn evalRvalue (.plain "evalRvalue")
  (doc! "Evaluate an rvalue to a runtime value. `use` forwards to `evalOperand`. The \
    reference-introducing case `ref` resolves the referenced place to a runtime address via \
    `evalPlace` and wraps the resulting thin pointer in #Value.ptr. The region and mutability are \
    presentation-only in this model: aliasing and mutation are tracked by the PCG analysis, not by \
    runtime metadata. Returns `None` when the referenced place cannot be resolved.")
  (m "The machine state." : Machine)
  (rv "The rvalue." : Rvalue)
  requires Runnable m
  : Option Value where
  | m ; .use o =>
      evalOperand m o proof[h_Runnable]
  | m ; .ref _ _ p =>
      let ⟨pp, _⟩ ←
        evalPlace m p proof[h_Runnable] ;
      Some Value.ptr pp↦ptr

end Machine
