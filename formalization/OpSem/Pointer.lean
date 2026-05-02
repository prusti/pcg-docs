import OpSem.Allocation
import MIR.Ty

defStruct Provenance (.sym .pi, .text "Provenance")
  "Provenances"
  (doc! "A pointer provenance \
    $π ∈ _Provenance_$, \
    identifying the allocation.")
where
  | id "The allocation identifier." : AllocId
  deriving DecidableEq, Repr, Hashable, Inhabited

defStruct ThinPointer (.raw "ptr", .text "ThinPointer")
  "Thin Pointers"
  (doc! "A thin pointer \
    $_ptr_ ∈ _ThinPointer_$: \
    an address together with optional provenance.")
where
  | addr "The address." : Address
  | provenance "The optional provenance." : Option Provenance
  deriving DecidableEq, Repr, Hashable, Inhabited

defEnum PointerMeta (.raw "meta", .text "PointerMeta")
  "Pointer Metadata"
  (doc! "Wide-pointer metadata \
    $_meta_ ∈ _PointerMeta_$. \
    Only the element-count case is modelled; vtable pointers \
    are not supported.")
where
  | elementCount (count : Nat)
    "Element count for slice-like wide pointers."
    (.text "elemCount ", #count (.raw "n"))
  deriving DecidableEq, Repr, Hashable

instance : Inhabited PointerMeta where
  default := .elementCount 0

defStruct Pointer (.bold (.raw "p"), .text "Pointer")
  "Pointers"
  (doc! "A pointer {.math (.seq [symDoc, .sym .setContains, setDoc])}: a thin pointer \
    together with optional wide-pointer metadata.")
where
  | thin "The underlying thin pointer." : ThinPointer
  | metadata "Optional wide-pointer metadata." : Option PointerMeta
  deriving DecidableEq, Repr, Hashable, Inhabited

defStruct TupleHeadLayout (.raw "thl",
    .text "TupleHeadLayout")
  "Tuple Head Layouts"
  (doc! "The layout of the head of a tuple type \
    $_thl_ ∈ _TupleHeadLayout_$. \
    Alignment information is omitted.")
where
  | endOffset "Offset at which the tuple head ends (in bytes)." : Nat
  deriving Repr, BEq, Hashable, Inhabited

defEnum LayoutStrategy (.raw "ls", .text "LayoutStrategy")
  "Layout Strategies"
  (doc! "A $_ls_ ∈ _LayoutStrategy_$ \
    describes how the size of a value can be determined. \
    Alignment is not tracked and trait objects are not \
    supported.")
where
  | sized (size : Nat)
    "A value of statically known size (in bytes)."
    (.text "sized ", #size (.raw "n"))
  | slice (elemSize : Nat)
    "A slice whose element has a statically known size (in bytes)."
    (.text "slice ", #elemSize (.raw "n"))
  | tuple (head : TupleHeadLayout) (tail : LayoutStrategy)
    "A tuple layout: a head layout followed by a tail layout."
  deriving Repr, BEq, Hashable

instance : Inhabited LayoutStrategy where
  default := .sized 0

defStruct PointeeInfo (.raw "pi", .text "PointeeInfo")
  "Pointee Information"
  (doc! "Information about a pointer's pointee \
    $_pi_ ∈ _PointeeInfo_$. \
    Only the layout is modelled; other fields from minirust \
    are omitted.")
where
  | layout "The layout strategy of the pointee." : LayoutStrategy
  deriving Repr, BEq, Hashable, Inhabited

defEnum PointerMetaKind (.raw "mk",
    .text "PointerMetaKind")
  "Pointer Metadata Kinds"
  (doc! "The statically known kind of metadata stored in a \
    pointer $_mk_ ∈ _PointerMetaKind_$. \
    The vtable-pointer case is omitted.")
where
  | none
    "No metadata (thin pointer)."
  | elementCount
    "Element-count metadata (for slice-like wide pointers)."
    (.text "elemCount")
  deriving Repr, BEq, Hashable, Inhabited

defEnum PtrType (.raw "pt", .text "PtrType")
  "Pointer Types"
  (doc! "Static type information about a pointer \
    $_pt_ ∈ _PtrType_$. \
    The vtable-pointer case is omitted.")
where
  | ref (mutbl : Mutability) (pointee : PointeeInfo)
    "A reference, tracking mutability and pointee information."
    (.text "&", #mutbl, .text " ", #pointee)
  | box (pointee : PointeeInfo)
    "An owned box pointer."
  | raw (metaKind : PointerMetaKind)
    "A raw pointer, carrying only the kind of metadata."
  | fnPtr
    "A function pointer."
  deriving Repr, BEq, Hashable

instance : Inhabited PtrType where
  default := .fnPtr

namespace Allocation

defFn canAccess (.plain "can_access")
  (doc! "Whether the allocation is live and can be accessed at the given pointer for `len` bytes.")
  (alloc "The allocation." : Allocation)
  (ptr "The pointer." : ThinPointer)
  (len "The access length in bytes." : Nat)
  : Bool :=
    alloc↦live
      ∧ alloc↦address ≤ ptr↦addr ≤ ptr↦addr + len ≤ endAddr alloc

end Allocation

