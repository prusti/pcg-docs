import MIR.Place
import Shared.DefFn

defStruct BasicBlockIdx (.text "bb")
  "An index into the list of basic blocks."
where
  | index "The basic block index." : Nat

defEnum Operand (.italic (.text "o"))
  "An operand in a MIR statement or terminator."
where
  | copy (place : Place)
    "Copy the value at a place."
    (.text "copy ", #place)
  | move (place : Place)
    "Move the value out of a place."
    (.text "move ", #place)
  deriving Repr

defEnum Rvalue (.italic (.text "rv"))
  "A right-hand side value in an assignment."
where
  | use (operand : Operand)
    "Use an operand directly."
    (.text "use(", #operand, .text ")")
  | ref (region : Region) (mutability : Mutability)
      (place : Place)
    "Create a reference to a place."
    (.text "\\&", #region, .text " ",
     #mutability, .text " ", #place)
  deriving Repr

defEnum Statement (.italic (.text "s"))
  "A MIR statement within a basic block."
where
  | assign (lhs : Place) (rhs : Rvalue)
    "Assign an rvalue to a place."
    (#lhs, .text " := ", #rhs)
  | storageLive (lcl : Local)
    "Mark a local's storage as live."
    (.text "StorageLive(", #lcl, .text ")")
  | storageDead (lcl : Local)
    "Mark a local's storage as dead."
    (.text "StorageDead(", #lcl, .text ")")
  deriving Repr

defEnum Terminator (.italic (.text "t"))
  "A basic block terminator."
where
  | goto (target : BasicBlockIdx)
    "Unconditional jump."
    (.text "goto ", #target)
  | switchInt (operand : Operand)
    "Switch on an integer value."
    (.text "switchInt(", #operand, .text ")")
  | return_
    "Return from the function."
    (.text "return")
  | unreachable
    "Marks unreachable code."
    (.text "unreachable")
  | drop (place : Place) (target : BasicBlockIdx)
    "Drop the value at a place."
    (.text "drop(",
     #place, .text ", ", #target, .text ")")
  deriving Repr

defStruct BasicBlock (.text "B")
  "A basic block: a sequence of statements followed \
   by a terminator."
where
  | statements "The statements in the block."
      : List Statement
  | terminator "The block's terminator." : Terminator
  deriving Repr

defStruct LocalDecls (.text "Δ")
  "Local variable declarations: a type for each local."
where
  | decls "The type of each local variable."
      : List Ty
  deriving Repr

defStruct Body (.text "body")
  "A MIR function body."
where
  | localDecls "The local variable declarations."
      : LocalDecls
  | basicBlocks "The basic blocks." : List BasicBlock
  deriving Repr

defStruct PlaceTy (.text "pty")
  "The type of a place: a type paired with an optional \
   variant index (set after a downcast)."
where
  | ty "The type." : Ty
  | variant "The variant index, if downcasted."
      : Option VariantIdx
  deriving Repr

defFn projTy (.text "projTy")
  "Project a type through a list of projection \
   elements. Returns the final PlaceTy after all \
   projections."
  (τ "The current type." : Ty)
  (v "The variant index." : Option VariantIdx)
  (projs "The projection elements." : List ProjElem)
  : Option PlaceTy where
  | ty ; v ; [] => Some PlaceTy⟨ty, v⟩
  | .ref _ _ pointee ; _ ; .deref :: rest =>
      projTy ‹pointee, None, rest›
  | .box inner ; _ ; .deref :: rest =>
      projTy ‹inner, None, rest›
  | _ ; _ ; .deref :: _ => None
  | _ ; _ ; (.field _ ty) :: rest =>
      projTy ‹ty, None, rest›
  | .array elem _ ; _ ; (.index _) :: rest =>
      projTy ‹elem, None, rest›
  | _ ; _ ; (.index _) :: _ => None
  | ty ; _ ; (.downcast v) :: rest =>
      projTy ‹ty, Some v, rest›

defFn ownedProjTy (.text "ownedProjTy")
  "Check whether a place is owned by walking its \
   projection list. Returns Some false as soon as \
   a dereference of a reference is encountered, \
   Some true if all projections are traversed \
   without dereferencing a reference, or None on \
   a type error."
  (τ "The current type." : Ty)
  (projs "The projection elements." : List ProjElem)
  : Option Bool where
  | _ ; [] => Some true
  | .ref _ _ _ ; .deref :: _ => Some false
  | .box inner ; .deref :: rest =>
      ownedProjTy ‹inner, rest›
  | _ ; .deref :: _ => None
  | _ ; (.field _ ty) :: rest =>
      ownedProjTy ‹ty, rest›
  | .array elem _ ; (.index _) :: rest =>
      ownedProjTy ‹elem, rest›
  | _ ; (.index _) :: _ => None
  | ty ; (.downcast _) :: rest =>
      ownedProjTy ‹ty, rest›

defFn isOwned (.text "isOwned")
  "Returns true iff a place is owned, i.e. it does \
   not project from the dereference of a \
   reference-typed place. See definitions/places.md."
  (body "The function body." : Body)
  (place "The place to type-check." : Place)
  : Option Bool begin
  let decls := body↦localDecls↦decls
  let baseIdx := place↦base↦index
  let τ₀ ← decls !! baseIdx
  return ownedProjTy ‹τ₀, place↦projection›

defFn placeTy (.text "ty")
  "Compute the type of a place: look up the base \
   local in Δ, then project through projections."
  (body "The function body." : Body)
  (place "The place to type-check." : Place)
  : Option PlaceTy begin
  let decls := body↦localDecls↦decls
  let baseIdx := place↦base↦index
  let τ₀ ← decls !! baseIdx
  return projTy ‹τ₀, None, place↦projection›
