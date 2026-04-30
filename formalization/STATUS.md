# Formalization Status

This document tracks how much of the
[MiniRust](https://github.com/minirust/minirust) operational semantics is
covered by the Lean 4 formalization in this directory. Each section corresponds
to a spec file in the MiniRust repository. Checkboxes indicate coverage:

- [x] = complete
- [~] = in progress
- [N] = not planned
- [U] = unsure (may ultimately not implement)
- [ ] = not yet implemented

---

## Prelude (`spec/prelude/`)

### [`main.md`](https://github.com/minirust/minirust/blob/master/spec/prelude/main.md) -- Core types

- [ ] `TerminationInfo` enum (Ub, MachineStop, Abort, IllFormed)

Will not include DeadLock or MemoryLeak

- [N] `Result<T>` / `NdResult<T>` type aliases
- [N] Error-throwing macros (`throw_ub!`, `throw_abort!`, ...)

### [`target.md`](https://github.com/minirust/minirust/blob/master/spec/prelude/target.md) -- Target specification

- [x] Pointer size (hardcoded to 8 bytes / 64-bit in `Ty.sizeBytes`)
- [N] `Target` trait (`PTR_SIZE`, `PTR_ALIGN`, `INT_MAX_ALIGN`, `ENDIANNESS`, `MAX_ATOMIC_SIZE`)
- [N] `valid_size()` method

---

## Memory Layer (`spec/mem/`)

### [`pointer.md`](https://github.com/minirust/minirust/blob/master/spec/mem/pointer.md) -- Pointer types

- [x] `Address` type &rarr; `Address.lean`
- [x] `ThinPointer` (address + optional provenance) &rarr; `Pointer.lean`
- [x] `Pointer` (thin pointer with optional wide-pointer metadata) &rarr; `Pointer.lean`
- [x] `PointerMeta` (only the ElementCount case) &rarr; `Pointer.lean`
- [x] `PtrType` enum (Ref, Box, Raw, FnPtr; VtablePtr excluded) &rarr; `Pointer.lean`
- [x] `PointeeInfo` struct (`layout` only) &rarr; `Pointer.lean`
- [x] `LayoutStrategy` enum (TraitObject excluded, no alignment) &rarr; `Pointer.lean`
- [x] `TupleHeadLayout` struct (no alignment) &rarr; `Pointer.lean`
- [N] `UnsafeCellStrategy`
- [x] `PointerMetaKind` enum (VTablePointer excluded) &rarr; `Pointer.lean`

### [`interface.md`](https://github.com/minirust/minirust/blob/master/spec/mem/interface.md) -- Memory interface

- [x] `AbstractByte` enum (Uninit, Init) &rarr; `AbstractByte.lean`
  - [N] Provenance on initialized bytes (minirust attaches optional provenance to each byte)
- [ ] `AllocationKind` enum (Stack, Heap, Global, Function, VTable)
- [N] `Memory` trait as a formal interface
- [~] Memory operations are implemented directly rather than via a trait:
  - [x] `allocate` &rarr; `Memory.allocate`
  - [x] `deallocate` &rarr; `Memory.deallocate`
  - [x] `store` &rarr; `Memory.store`
  - [x] `load` &rarr; `Memory.load`
  - [ ] `dereferenceable` / `signed_dereferenceable`
  - [N] `retag_ptr`
  - [N] `new_call` / `end_call`
  - [N] `leak_check`

### [`basic.md`](https://github.com/minirust/minirust/blob/master/spec/mem/basic.md) -- Basic memory model

- [x] `AllocId` &rarr; `Allocation.lean`
- [x] `Allocation` struct (id, data, address, live) &rarr; `Allocation.lean`
  - [U] `Allocation.kind` field (AllocationKind)
  - [U] `Allocation.align` field
- [x] `allocate` (creates new allocation with uninit bytes) &rarr; `Memory.allocate`
  - [~] Address selection is deterministic (top-of-heap), not non-deterministic as in minirust
- [x] `deallocate` (marks allocation as dead) &rarr; `Memory.deallocate`
  - [ ] Validation checks (double-free, alignment, metadata consistency)
- [x] `store` (write bytes with bounds checking) &rarr; `Memory.store`
  - [N] Alignment checking
- [x] `load` (read bytes with bounds checking) &rarr; `Memory.load`
  - [N] Alignment checking
- [x] `check_ptr` helper (provenance, liveness, bounds) &rarr; `Memory.checkPtr`
- [N] `leak_check`

### [`concurrent.md`](https://github.com/minirust/minirust/blob/master/spec/mem/concurrent.md) -- Concurrent memory

Will not implement

- [N] `ConcurrentMemory` wrapper
- [N] `Atomicity` enum
- [N] `AccessType` / `Access` structs
- [N] Data race detection (`check_data_races`, `races`)

### [`intptrcast.md`](https://github.com/minirust/minirust/blob/master/spec/mem/intptrcast.md) -- Integer-pointer casts

- [N] `IntPtrCast` struct
- [N] `expose` (pointer-to-integer cast provenance tracking)
- [N] `int2ptr` (integer-to-pointer cast with non-deterministic provenance)

### Tree Borrows (`spec/mem/tree_borrows/`)

Will not implement


## Language Layer (`spec/lang/`)

### [`values.md`](https://github.com/minirust/minirust/blob/master/spec/lang/values.md) -- Values

- [x] `Value` enum &rarr; `Value.lean`
  - [x] `Bool`
  - [x] `Int`
  - [x] `Tuple`
  - [~] `Array` (in Value enum but encode/decode not implemented)
  - [ ] `Ptr`
  - [ ] `Variant`
  - [N] `Union`
- [~] `Place` struct (simplified as `PlacePtr` with just a `ThinPointer`)
  - [U] `aligned` field

### [`types.md`](https://github.com/minirust/minirust/blob/master/spec/lang/types.md) -- Types

- [x] `IntType` (signedness + size) &rarr; `Ty.lean`
- [~] `Type` enum &rarr; `Ty` in `Ty.lean`
  - [x] `Bool`
  - [x] `Int`
  - [x] `Ref` (region + mutability + pointee, modeled as `Ty.ref`)
  - [x] `Box`
  - [x] `Array`
  - [~] ADTs (modeled via `Ty.ctor` with type constructor names)
  - [x] Type parameters (`Ty.param`)
  - [x] Alias types (`Ty.alias`)
  - [N] `Ptr` (raw pointers)
  - [ ] `Tuple` (as a distinct type; currently subsumed by `ctor`)
  - [N] `Union`
  - [ ] `Enum`
  - [ ] `Slice`
  - [N] `TraitObject`
- [x] `Size` enum (fixed bits, pointer-sized) &rarr; `Ty.lean`
- [x] `sizeBytes` function &rarr; `Ty.lean`
- [ ] `Fields` type (offset-type pairs)
- [ ] `Variant` struct (for enums)
- [ ] `Discriminator` decision tree
- [ ] Layout computation functions (don't compute alignment)

### [`syntax.md`](https://github.com/minirust/minirust/blob/master/spec/lang/syntax.md) -- Abstract syntax

**Value expressions:**
- [~] `ValueExpr` enum &rarr; `Expressions.lean` (only `Tuple` variant)
  - [x] Tuple
  - [ ] Constant (exclude VTablePointer)
  - [N] Union
  - [ ] Variant
  - [ ] GetDiscriminant
  - [ ] Load
  - [ ] AddrOf
  - [ ] UnOp
  - [ ] BinOp

**Place expressions:**
- [~] Place + projection system covers the same ground as minirust's `PlaceExpr`:
  - [x] Local &rarr; `Place.lean`
  - [x] Deref &rarr; `ProjElem.deref`
  - [x] Field &rarr; `ProjElem.field`
  - [x] Index &rarr; `ProjElem.index`
  - [x] Downcast &rarr; `ProjElem.downcast`

**Operands (MIR-level; not in minirust):**
- [x] `Operand` enum (Copy, Move, Const) &rarr; `Body.lean`

**Rvalues (MIR-level; not in minirust -- minirust's `Statement::Assign` directly uses `ValueExpr`):**
- [~] `Rvalue` enum &rarr; `Body.lean`
  - [x] Use
  - [x] Ref
  - [ ] Other rvalue kinds (BinaryOp, UnaryOp, Aggregate, etc.)

**Statements:**
- [~] `Statement` enum &rarr; `Body.lean`
  - [x] Assign
  - [x] StorageLive
  - [x] StorageDead
  - [ ] PlaceMention
  - [ ] SetDiscriminant
  - [ ] Validate
  - [ ] Deinit

**Terminators:**
- [~] `Terminator` enum &rarr; `Body.lean`
  - [x] Goto
  - [x] SwitchInt (minirust: `Switch`)
  - [x] Return
  - [x] Unreachable
  - [x] Call
  - [x] Drop (MIR-level; not in minirust)
  - [ ] Intrinsic
  - [ ] StartUnwind / StopUnwind / ResumeUnwind

**Constants:**
- [~] `ConstValue` enum &rarr; `ConstValue.lean`
  - [x] Bool
  - [x] Int
  - [x] Tuple
  - [x] Array
  - [ ] GlobalPointer
  - [ ] FnPointer
  - [ ] VTablePointer
  - [ ] PointerWithoutProvenance

**Operators:**
- [ ] `UnOp` enum (IntUnOp, CastOp, ...)
- [ ] `BinOp` enum (IntBinOp, RelOp, PtrOffset, ...)

**Program structure:**
- [x] `BasicBlock` (statements + terminator) &rarr; `Body.lean`
- [x] `Body` (local declarations + basic blocks) &rarr; `Body.lean`
- [x] `Location` (block index + statement index) &rarr; `Body.lean`
- [ ] `Program` struct (functions, start, globals, traits, vtables)
- [ ] `Function` struct (locals, args, ret, calling_convention, blocks)
- [ ] `Global` / `Relocation` / `VTable`
- [ ] `CallingConvention` enum
- [ ] `IntrinsicOp` enum
- [ ] `BbKind` enum
- [ ] Name types (`FnName`, `GlobalName`, etc.)

### [`representation.md`](https://github.com/minirust/minirust/blob/master/spec/lang/representation.md) -- Encode/Decode

- [x] Bool encode/decode &rarr; `Decode.lean`
- [~] Integer encode/decode &rarr; `Decode.lean`
  - [x] Unsigned integers (little-endian)
  - [ ] Signed integers
  - [N] Endianness parameterization
- [ ] Pointer encode/decode
- [ ] Tuple encode/decode (recursive field-by-field)
- [ ] Array encode/decode (element-by-element)
- [N] Union encode/decode (raw bytes)
- [ ] Enum encode/decode (discriminant tree)
- [N] Unsized type handling (Slice, TraitObject)
- [x] `typed_load` &rarr; `Machine.typedLoad`
- [x] `typed_store` &rarr; `Machine.typedStore`
- [N] `check_value` (well-formed value validation)
- [N] `transmute`

### [`well-formed.md`](https://github.com/minirust/minirust/blob/master/spec/lang/well-formed.md) -- Well-formedness

- [x] Place well-formedness (`validPlace`, `validProjTy`) &rarr; `Body.lean`
- [x] Body well-formedness (`validBody`) &rarr; `Body.lean`
- [N] `IntType::check_wf`
- [N] `Type::check_wf`
- [N] `PtrType::check_wf`
- [N] `Constant::check_wf`
- [N] `ValueExpr::check_wf`
- [N] `PlaceExpr::check_wf`
- [N] `Statement::check_wf`
- [N] `Terminator::check_wf`
- [N] `Function::check_wf`
- [N] `Program::check_wf`
- [N] `Discriminator::check_wf`

### [`machine.md`](https://github.com/minirust/minirust/blob/master/spec/lang/machine.md) -- Abstract Machine

- [~] `Machine` struct &rarr; `Machine.lean`
  - [x] Function body
  - [x] Program counter (`Location`)
  - [x] Local variable storage (map from Local to ThinPointer)
  - [x] Memory
  - [N] Thread collection / active thread tracking
  - [N] Lock state
  - [N] Global/function/vtable pointer maps
  - [N] Stdout/stderr streams
- [N] `StackFrame` struct
- [N] `StackPopAction` enum
- [N] `Thread` / `ThreadState`
- [ ] `Machine::new()` (program initialization)
- [ ] `Machine::step()` (main transition function)
- [N] Function/vtable pointer lookup

### [`step/statements.md`](https://github.com/minirust/minirust/blob/master/spec/lang/step/statements.md) -- Statement evaluation

- [x] `placeStore` / `placeLoad` helpers &rarr; `Statements.lean`
- [ ] `eval_statement` dispatch
  - [~] Assign (store/load primitives exist, but no full assignment evaluation)
  - [ ] PlaceMention
  - [ ] SetDiscriminant
  - [N] Validate (retag)
  - [ ] Deinit
  - [ ] StorageLive (allocation in eval)
  - [ ] StorageDead (deallocation in eval)

### [`step/terminators.md`](https://github.com/minirust/minirust/blob/master/spec/lang/step/terminators.md) -- Terminator evaluation

- [ ] `eval_terminator` dispatch
- [ ] Goto evaluation
- [ ] Switch evaluation
- [ ] Unreachable evaluation
- [ ] Call evaluation
  - [N] ABI Checks
  - [N] Create Frame
- [ ] Return evaluation
 - [N] Frame pop
- [N] Unwinding (StartUnwind, StopUnwind, ResumeUnwind)
- [N] Intrinsic call evaluation

### [`step/expressions.md`](https://github.com/minirust/minirust/blob/master/spec/lang/step/expressions.md) -- Expression evaluation

**Value expressions (`eval_value`):**
- [~] Implemented for tuple only &rarr; `Expressions.lean`
  - [x] Tuple construction
  - [ ] Constant evaluation
  - [N] Union construction
  - [ ] Enum variant construction
  - [ ] GetDiscriminant
  - [x] Load from memory (Place load)
  - [ ] AddrOf (creating references)
  - [ ] UnOp / BinOp

**Place expressions (`eval_place`):**
- [~] Place evaluation &rarr; `Expressions/Place.lean`
  - [x] `evalLocal`
  - [x] `evalPlace` (dispatcher over projection list)
  - [x] `evalProjs` (thread place/type through projections)
  - [x] Field projection evaluation (`evalField`, with `fieldOffset`)
  - [ ] Deref evaluation
  - [ ] Index evaluation
  - [ ] Downcast evaluation

### [`step/operators.md`](https://github.com/minirust/minirust/blob/master/spec/lang/step/operators.md) -- Operator evaluation

**Unary operators:**
- [ ] `eval_un_op` dispatch
- [ ] Integer operation
  - [ ] Neg
  - [N] BitNot
  - [N] CountOnes
- [N] Cast operations (IntToInt, Transmute)
- [N] Wide pointer operators (GetThinPointer, GetMetadata)
- [N] ComputeSize / ComputeAlign
- [N] VTableMethodLookup

**Binary operators:**
- [ ] `eval_bin_op` dispatch
- [ ] Integer arithmetic (Add, Sub, Mul, Div, Rem, Shl, Shr, ...)
- [ ] Integer with overflow
- [ ] Relational operators (Lt, Gt, Le, Ge, Eq, Ne, Cmp)
- [N] Pointer arithmetic (PtrOffset, PtrOffsetFrom)
- [N] ConstructWidePointer

### [`step/intrinsics.md`](https://github.com/minirust/minirust/blob/master/spec/lang/step/intrinsics.md) -- Intrinsics

No implementation for now

<!--
- [ ] Pointer provenance (PointerExposeProvenance, PointerWithExposedProvenance)
- [ ] Machine primitives (Exit, Abort)
- [ ] UB control (Assume)
- [ ] I/O (PrintStdout, PrintStderr)
- [ ] Heap memory (Allocate, Deallocate)
- [ ] Threads (Spawn, Join)
- [ ] RawEq
- [ ] Atomic accesses (AtomicStore, AtomicLoad, AtomicCompareExchange, AtomicFetchAndOp)
- [ ] GetUnwindPayload
-->

### [`step/locks.md`](https://github.com/minirust/minirust/blob/master/spec/lang/step/locks.md) -- Locks

No implementation for now

<!-- - [ ] `LockState` enum
- [ ] `lock_create`
- [ ] `lock_acquire`
- [ ] `lock_release`
- [ ] Lock intrinsic dispatch -->
