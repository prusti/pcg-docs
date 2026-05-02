import OpSem.Allocation
import MIR.Ty

defStruct Provenance (.raw "\\pi", .text "Provenance")
  "Provenances"
  (.seq [.plain "A pointer provenance ",
    .math (.seq [.raw "\\pi", .sym .setContains, .text "Provenance"]),
    .plain ", identifying the allocation."])
where
  | id "The allocation identifier." : AllocId
  deriving DecidableEq, Repr, Hashable, Inhabited

defStruct ThinPointer (.raw "ptr", .text "ThinPointer")
  "Thin Pointers"
  (.seq [.plain "A thin pointer ",
    .math (.seq [.raw "ptr", .sym .setContains, .text "ThinPointer"]),
    .plain ": an address together with optional provenance."])
where
  | addr "The address." : Address
  | provenance "The optional provenance." : Option Provenance
  deriving DecidableEq, Repr, Hashable, Inhabited

defEnum PointerMeta (.raw "meta", .text "PointerMeta")
  "Pointer Metadata"
  (.seq [.plain "Wide-pointer metadata ",
    .math (.seq [.raw "meta", .sym .setContains, .text "PointerMeta"]),
    .plain ". Only the element-count case is modelled; vtable \
    pointers are not supported."])
where
  | elementCount (count : Nat)
    "Element count for slice-like wide pointers."
    (.text "elemCount ", #count (.raw "n"))
  deriving DecidableEq, Repr, Hashable

instance : Inhabited PointerMeta where
  default := .elementCount 0

defStruct Pointer (.bold (.raw "p"), .text "Pointer")
  "Pointers"
  (.seq [.plain "A pointer ",
    .math (.seq [symDoc, .sym .setContains, setDoc]),
    .plain ": a thin pointer together with optional wide-pointer \
    metadata."])
where
  | thin "The underlying thin pointer." : ThinPointer
  | metadata "Optional wide-pointer metadata." : Option PointerMeta
  deriving DecidableEq, Repr, Hashable, Inhabited

defStruct TupleHeadLayout (.raw "thl",
    .text "TupleHeadLayout")
  "Tuple Head Layouts"
  (.seq [.plain "The layout of the head of a tuple type ",
    .math (.seq [.raw "thl", .sym .setContains, .text "TupleHeadLayout"]),
    .plain ". Alignment information is omitted."])
where
  | endOffset "Offset at which the tuple head ends (in bytes)." : Nat
  deriving Repr, BEq, Hashable, Inhabited

defEnum LayoutStrategy (.raw "ls", .text "LayoutStrategy")
  "Layout Strategies"
  (.seq [.plain "A ",
    .math (.seq [.raw "ls", .sym .setContains, .text "LayoutStrategy"]),
    .plain " describes how the size of a value can be \
    determined. Alignment is not tracked and trait objects are \
    not supported."])
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
  (.seq [.plain "Information about a pointer's pointee ",
    .math (.seq [.raw "pi", .sym .setContains, .text "PointeeInfo"]),
    .plain ". Only the layout is modelled; other fields from \
    minirust are omitted."])
where
  | layout "The layout strategy of the pointee." : LayoutStrategy
  deriving Repr, BEq, Hashable, Inhabited

defEnum PointerMetaKind (.raw "mk",
    .text "PointerMetaKind")
  "Pointer Metadata Kinds"
  (.seq [.plain "The statically known kind of metadata stored \
    in a pointer ",
    .math (.seq [.raw "mk", .sym .setContains, .text "PointerMetaKind"]),
    .plain ". The vtable-pointer case is omitted."])
where
  | none
    "No metadata (thin pointer)."
  | elementCount
    "Element-count metadata (for slice-like wide pointers)."
    (.text "elemCount")
  deriving Repr, BEq, Hashable, Inhabited

defEnum PtrType (.raw "pt", .text "PtrType")
  "Pointer Types"
  (.seq [.plain "Static type information about a pointer ",
    .math (.seq [.raw "pt", .sym .setContains, .text "PtrType"]),
    .plain ". The vtable-pointer case is omitted."])
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
      ∧ alloc↦address ≤ ptr↦addr ≤ ptr↦addr + len ≤ endAddr ‹alloc›

end Allocation

