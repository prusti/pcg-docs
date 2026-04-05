import MIR.Place
import Core.Dsl.DefFn
import Core.Dsl.DefProperty

defStruct BasicBlockIdx (.text "bb")
  "An index into the list of basic blocks."
where
  | index "The basic block index." : Nat

defEnum Operand (.math (.var "o"))
  "An operand in a MIR statement or terminator."
where
  | copy (place : Place)
    "Copy the value at a place."
    (.doc (.text "copy "), #place)
  | move (place : Place)
    "Move the value out of a place."
    (.doc (.text "move "), #place)
  | const (val : Value)
    "A constant value."
    (.doc (.text "const "), #val)
  deriving Repr, BEq, Hashable

namespace Operand

defFn operandPlace (.text "operandPlace")
  "Extract the place from an operand, if any."
  (o "The operand." : Operand)
  : Option Place where
  | .copy p => Some p
  | .move p => Some p
  | .const _ => None

end Operand

defEnum Rvalue (.math (.var "rv"))
  "A right-hand side value in an assignment."
where
  | use (operand : Operand)
    "Use an operand directly."
    (.doc (.text "use"), .sym .lparen,
     #operand, .sym .rparen)
  | ref (region : Region) (mutability : Mutability)
      (place : Place)
    "Create a reference to a place."
    (.doc (.code "&"), #region, .doc (.text " "),
     #mutability, .doc (.text " "), #place)
  deriving Repr, BEq, Hashable

namespace Rvalue

defFn rvaluePlace (.text "rvaluePlace")
  "Extract the place from an rvalue, if any."
  (rv "The rvalue." : Rvalue)
  : Option Place where
  | .use o => o·operandPlace
  | .ref _ _ p => Some p

end Rvalue

defEnum Statement (.math (.var "s"))
  "A MIR statement within a basic block."
where
  | assign (lhs : Place) (rhs : Rvalue)
    "Assign an rvalue to a place."
    (#lhs, .doc (.text " := "), #rhs)
  | storageLive (lcl : Local)
    "Mark a local's storage as live."
    (.doc (.text "StorageLive"), .sym .lparen,
     #lcl, .sym .rparen)
  | storageDead (lcl : Local)
    "Mark a local's storage as dead."
    (.doc (.text "StorageDead"), .sym .lparen,
     #lcl, .sym .rparen)
  deriving Repr, BEq, Hashable

namespace Statement

defFn statementPlaces (.text "statementPlaces")
  "Extract all places referenced by a statement."
  (s "The statement." : Statement)
  : Set Place where
  | .assign lhs rhs =>
      ⦃lhs⦄ ∪ (rhs·rvaluePlace)·toSet
  | .storageLive _ => ∅
  | .storageDead _ => ∅

end Statement

defEnum Terminator (.math (.var "t"))
  "A basic block terminator."
where
  | goto (target : BasicBlockIdx)
    "Unconditional jump."
    (.doc (.text "goto "), #target)
  | switchInt (operand : Operand)
    "Switch on an integer value."
    (.doc (.text "switchInt"), .sym .lparen,
     #operand, .sym .rparen)
  | return_
    "Return from the function."
    (.doc (.text "return"))
  | unreachable
    "Marks unreachable code."
    (.doc (.text "unreachable"))
  | drop (place : Place) (target : BasicBlockIdx)
    "Drop the value at a place."
    (.doc (.text "drop"), .sym .lparen,
     #place, .doc (.text ", "), #target,
     .sym .rparen)
  | call (callee : Operand) (args : List Operand)
      (targetPlace : Place)
      (nextBlock : BasicBlockIdx)
    "Call a function."
    (#callee, .sym .lparen,
     #args (.var "\\bar{o}"),
     .sym .rparen, .doc (.text " → "),
     #targetPlace, .doc (.text ", "), #nextBlock)
  deriving Repr, BEq, Hashable

namespace Terminator

defFn terminatorPlaces (.text "terminatorPlaces")
  "Extract all places referenced by a terminator."
  (t "The terminator." : Terminator)
  : Set Place where
  | .goto _ => ∅
  | .switchInt o => o·operandPlace·toSet
  | .return_ => ∅
  | .unreachable => ∅
  | .drop p _ => ⦃p⦄
  | .call callee args dest _ =>
      ⦃dest⦄ ∪ callee·operandPlace·toSet ∪ (args·setFlatMap fun a => a·operandPlace·toSet)

end Terminator

defStruct BasicBlock (.math (.var "B"))
  "A basic block: a sequence of statements followed \
   by a terminator."
where
  | statements "The statements in the block."
      : List Statement
  | terminator "The block's terminator." : Terminator
  deriving Repr, BEq, Hashable

namespace BasicBlock

defFn basicBlockPlaces (.text "basicBlockPlaces")
  "All places referenced in a basic block."
  (bb "The basic block." : BasicBlock)
  : Set Place where
  | ⟨stmts, t⟩ =>
      (stmts·setFlatMap fun s => s·statementPlaces) ∪ t·terminatorPlaces

end BasicBlock

defStruct Body (.text "body")
  "A MIR function body."
where
  | decls "The local variable declarations."
      : List Ty
  | basicBlocks "The basic blocks." : List BasicBlock
  deriving Repr, BEq, Hashable

namespace Body

defFn bodyPlaces (.text "bodyPlaces")
  "All places referenced in a function body."
  (body "The function body." : Body)
  : Set Place where
  | ⟨_, bbs⟩ =>
      bbs·setFlatMap fun bb => bb·basicBlockPlaces

end Body

defStruct PlaceTy (.text "pty")
  "The type of a place: a type paired with an optional \
   variant index (set after a downcast)."
where
  | ty "The type." : Ty
  | variant "The variant index, if downcasted."
      : Option VariantIdx
  deriving Repr, BEq, Hashable

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

defProperty validProjTy (.text "validProjTy")
  "A type is valid for a projection list iff \
   projTy returns Some."
  (τ "The current type." : Ty)
  (projs "The projection elements." : List ProjElem)
  latex
    (.seq [.text "A type ",
           .math (.var "\\tau"),
           .text " is ",
           .italic (.text "valid"),
           .text " for a projection list ",
           .math (.var "\\pi"),
           .text " iff ",
           .code "projTy(τ, \\_, π)",
           .text " returns ",
           .code "Some \\_",
           .text "."])
  where
  | _ ; [] => true
  | .ref _ _ pointee ; .deref :: π =>
      validProjTy ‹pointee, π›
  | .box inner ; .deref :: π =>
      validProjTy ‹inner, π›
  | _ ; (.field _ τ) :: π =>
      validProjTy ‹τ, π›
  | .array elem _ ; (.index _) :: π =>
      validProjTy ‹elem, π›
  | τ ; (.downcast _) :: π =>
      validProjTy ‹τ, π›
  | _ ; _ :: _ => false

defFn isOwned' (.text "isOwned'")
  "Check whether a place is owned by walking its \
   projection list. Returns false as soon as a \
   dereference of a reference is encountered, \
   true if all projections are traversed without \
   dereferencing a reference."
  (τ "The current type." : Ty)
  (projs "The projection elements." : List ProjElem)
  : Bool where
  | _ ; [] => true
  | .ref _ _ _ ; .deref :: _ => false
  | .box inner ; .deref :: π =>
      isOwned' ‹inner, π›
  | _ ; (.field _ τ) :: π =>
      isOwned' ‹τ, π›
  | .array elem _ ; (.index _) :: π =>
      isOwned' ‹elem, π›
  | τ ; (.downcast _) :: π =>
      isOwned' ‹τ, π›
  | _ ; _ :: _ => false

defProperty validPlace (.text "valid")
  "A place is valid for a body."
  (body "The function body." : Body)
  (place "The place." : Place)
  latex
    (.seq [.text "A place ", .math (.var "p"),
           .text " is ",
           .italic (.text "valid"),
           .text " for a body ",
           .math (.var "body"),
           .text " iff its local index ",
           .code "p.base.index",
           .text " is less than ",
           .code "|body.decls|",
           .text " and ",
           .code "validProjTy(body.decls[p.base.index], p.projection)",
           .text " holds."])
  where
    | body ; p =>
        p↦base↦index < body↦decls·length ∧
        validProjTy ‹body↦decls ! p↦base↦index, p↦projection›

defProperty validBody (.text "validBody")
  "A body is valid iff all places in it are valid."
  (body "The function body." : Body)
  latex
    (.seq [.text "A body ",
           .math (.var "body"),
           .text " is ",
           .italic (.text "valid"),
           .text " iff every place in ",
           .code "bodyPlaces(body)",
           .text " is valid for ",
           .math (.var "body"),
           .text "."])
  where
    | body =>
        body·bodyPlaces·forAll fun p => validPlace ‹body, p›

defFn placeTy (.text "ty")
  "Compute the type of a place: look up the base \
   local in Δ, then project through projections."
  (body "The function body." : Body)
  (place "The place to type-check." : Place)
  requires validPlace(body, place)
  : Option PlaceTy begin
  return projTy ‹body↦decls ! place↦base↦index, None, place↦projection›

defFn isOwned (.text "isOwned")
  "Returns true iff a place is owned, i.e. it does \
   not project from the dereference of a \
   reference-typed place. See definitions/places.md."
  (body "The function body." : Body)
  (place "The place to type-check." : Place)
  requires validPlace(body, place)
  : Bool where
  | body ; place =>
      isOwned' ‹body↦decls ! place↦base↦index, place↦projection›
