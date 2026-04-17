import OpSem.Allocation
import MIR.Ty

defStruct Provenance (.raw "\\pi", .doc (.plain "Provenance"))
  "Provenances"
  "A pointer provenance {def}, identifying the allocation."
where
  | id "The allocation identifier." : AllocId
  deriving DecidableEq, Repr, Hashable, Inhabited

defStruct ThinPointer (.raw "ptr", .doc (.plain "ThinPointer"))
  "Thin Pointers"
  "A thin pointer {def}: an address together with optional provenance."
where
  | addr "The address." : Address
  | provenance "The optional provenance." : Option Provenance
  deriving DecidableEq, Repr, Hashable, Inhabited

defEnum PointerMeta (.raw "meta", .doc (.plain "PointerMeta"))
  "Pointer Metadata"
  "Wide-pointer metadata {def}. Only the element-count case is \
   modelled; vtable pointers are not supported."
where
  | elementCount (count : Nat)
    "Element count for slice-like wide pointers."
    (.doc (.plain "elemCount "), #count (.raw "n"))
  deriving DecidableEq, Repr, Hashable

instance : Inhabited PointerMeta where
  default := .elementCount 0

defStruct Pointer (.raw "\\hat{p}", .doc (.plain "Pointer"))
  "Pointers"
  "A pointer {def}: a thin pointer together with optional \
   wide-pointer metadata."
where
  | thin "The underlying thin pointer." : ThinPointer
  | metadata "Optional wide-pointer metadata." : Option PointerMeta
  deriving DecidableEq, Repr, Hashable, Inhabited

defStruct TupleHeadLayout (.raw "thl",
    .doc (.plain "TupleHeadLayout"))
  "Tuple Head Layouts"
  "The layout of the head of a tuple type {def}. \
   Alignment information is omitted."
where
  | endOffset "Offset at which the tuple head ends (in bytes)." : Nat
  deriving Repr, BEq, Hashable, Inhabited

defEnum LayoutStrategy (.raw "ls", .doc (.plain "LayoutStrategy"))
  "Layout Strategies"
  "A {def} describes how the size of a value can be determined. \
   Alignment is not tracked and trait objects are not supported."
where
  | sized (size : Nat)
    "A value of statically known size (in bytes)."
    (.doc (.plain "sized "), #size (.raw "n"))
  | slice (elemSize : Nat)
    "A slice whose element has a statically known size (in bytes)."
    (.doc (.plain "slice "), #elemSize (.raw "n"))
  | tuple (head : TupleHeadLayout) (tail : LayoutStrategy)
    "A tuple layout: a head layout followed by a tail layout."
    (.doc (.plain "tuple "), #head, .doc (.plain ", "),
     #tail (.raw "ls"))
  deriving Repr, BEq, Hashable

instance : Inhabited LayoutStrategy where
  default := .sized 0

defStruct PointeeInfo (.raw "pi", .doc (.plain "PointeeInfo"))
  "Pointee Information"
  "Information about a pointer's pointee {def}. Only the layout is \
   modelled; other fields from minirust are omitted."
where
  | layout "The layout strategy of the pointee." : LayoutStrategy
  deriving Repr, BEq, Hashable, Inhabited

defEnum PointerMetaKind (.raw "mk",
    .doc (.plain "PointerMetaKind"))
  "Pointer Metadata Kinds"
  "The statically known kind of metadata stored in a pointer {def}. \
   The vtable-pointer case is omitted."
where
  | none
    "No metadata (thin pointer)."
    (.doc (.plain "none"))
  | elementCount
    "Element-count metadata (for slice-like wide pointers)."
    (.doc (.plain "elemCount"))
  deriving Repr, BEq, Hashable, Inhabited

defEnum PtrType (.raw "pt", .doc (.plain "PtrType"))
  "Pointer Types"
  "Static type information about a pointer {def}. The vtable-pointer \
   case is omitted."
where
  | ref (mutbl : Mutability) (pointee : PointeeInfo)
    "A reference, tracking mutability and pointee information."
    (.doc (.plain "&"), #mutbl, .doc (.plain " "), #pointee)
  | box (pointee : PointeeInfo)
    "An owned box pointer."
    (.doc (.code "Box"), .sym .langle, #pointee, .sym .rangle)
  | raw (metaKind : PointerMetaKind)
    "A raw pointer, carrying only the kind of metadata."
    (.doc (.plain "raw "), #metaKind)
  | fnPtr
    "A function pointer."
    (.doc (.plain "fnPtr"))
  deriving Repr, BEq, Hashable

instance : Inhabited PtrType where
  default := .fnPtr

namespace Allocation

defFn canAccess (.plain "can_access")
  (.seq [.plain "Whether the allocation is live and can \
    be accessed at the given pointer for ", .code "len",
    .plain " bytes."])
  (alloc "The allocation." : Allocation)
  (ptr "The pointer." : ThinPointer)
  (len "The access length in bytes." : Nat)
  : Bool :=
    alloc↦live
      ∧ alloc↦address ≤ ptr↦addr ≤ ptr↦addr + len ≤ endAddr ‹alloc›

end Allocation

