import MIR.Place
import Core.Dsl.DefFn
import Core.Dsl.DefProperty

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
    (.code (.text "&"), #region, .text " ",
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

defStruct Body (.text "body")
  "A MIR function body."
where
  | decls "The local variable declarations."
      : List Ty
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
  | τ ; v ; [] => Some PlaceTy⟨τ, v⟩
  | .ref _ _ pointee ; _ ; .deref :: π =>
      projTy ‹pointee, None, π›
  | .box inner ; _ ; .deref :: π =>
      projTy ‹inner, None, π›
  | _ ; _ ; (.field _ τ) :: π =>
      projTy ‹τ, None, π›
  | .array elem _ ; _ ; (.index _) :: π =>
      projTy ‹elem, None, π›
  | τ ; _ ; (.downcast v) :: π =>
      projTy ‹τ, Some v, π›
  | _ ; _ ; _ :: _ => None

defFn ownedProjTy (.text "ownedProjTy")
  "Check whether a place is owned by walking its projection list. Returns Some
  false as soon as a dereference of a reference is encountered, Some true if all
  projections are traversed without dereferencing a reference, or None on a
  type error."
  (τ "The current type." : Ty)
  (projs "The projection elements." : List ProjElem)
  : Option Bool where
  | _ ; [] => Some true
  | .ref _ _ _ ; .deref :: _ => Some false
  | .box inner ; .deref :: π =>
      ownedProjTy ‹inner, π›
  | _ ; (.field _ τ) :: π =>
      ownedProjTy ‹τ, π›
  | .array elem _ ; (.index _) :: π =>
      ownedProjTy ‹elem, π›
  | τ ; (.downcast _) :: π =>
      ownedProjTy ‹τ, π›
  | _ ; _ :: _ => None


defProperty validPlace (.text "valid")
  "A place is valid for a body."
  (body "The function body." : Body)
  (place "The place." : Place)
  latex
    (.seq [.text "A place ", .italic (.text "p"),
           .text " is ",
           .italic (.text "valid"),
           .text " for a body ",
           .italic (.text "body"),
           .text " iff its local index ",
           .code (.text "p.base.index"),
           .text " is less than ",
           .code (.text "|body.decls|"),
           .text "."])
  where
    | body ; p =>
        p↦base↦index < body↦decls·length

defFn placeTy (.text "ty")
  "Compute the type of a place: look up the base \
   local in Δ, then project through projections."
  (body "The function body." : Body)
  (place "The place to type-check." : Place)
  requires validPlace
  : Option PlaceTy begin
  return projTy ‹body↦decls ! place↦base↦index, None, place↦projection›

defFn isOwned (.text "isOwned")
  "Returns true iff a place is owned, i.e. it does \
   not project from the dereference of a \
   reference-typed place. See definitions/places.md."
  (body "The function body." : Body)
  (place "The place to type-check." : Place)
  requires validPlace
  : Option Bool begin
  return ownedProjTy ‹body↦decls ! place↦base↦index, place↦projection›
