import MIR.Place
import MIR.ConstValue
import Core.Dsl.DefFn
import Core.Dsl.DefProperty

defStruct BasicBlockIdx (.doc (.plain "bb"),
    .doc (.plain "BasicBlockIdx"))
  "Basic Block Indices"
  "An index into the list of basic blocks."
where
  | index "The basic block index." : Nat

defStruct Location (.raw "\\ell", .doc (.plain "Location"))
  "Locations"
  "A location in the MIR, identifying a statement \
   within a basic block."
where
  | block "The basic block." : BasicBlockIdx
  | stmtIdx "The statement index within the block." : Nat

defEnum Operand (.raw "o", .raw "O")
  "Operands"
  "An operand in a MIR statement or terminator."
where
  | copy (place : Place)
    "Copy the value at a place."
    (.doc (.plain "copy "), #place)
  | move (place : Place)
    "Move the value out of a place."
    (.doc (.plain "move "), #place)
  | const (val : ConstValue)
    "A constant value."
    (.doc (.plain "const "), #val)
  deriving Repr, BEq, Hashable

namespace Operand

defFn operandPlace (.plain "operandPlace")
  (.plain "Extract the place from an operand, if any.")
  (o "The operand." : Operand)
  : Option Place where
  | .copy p => Some p
  | .move p => Some p
  | .const _ => None

end Operand

defEnum Rvalue (.raw "rv", .raw "Rv")
  "Rvalues"
  "A right-hand side value in an assignment."
where
  | use (operand : Operand)
    "Use an operand directly."
    (.doc (.plain "use"), .sym .lparen,
     #operand, .sym .rparen)
  | ref (region : Region) (mutability : Mutability)
      (place : Place)
    "Create a reference to a place."
    (.doc (.code "&"), #region, .doc (.plain " "),
     #mutability, .doc (.plain " "), #place)
  deriving Repr, BEq, Hashable

namespace Rvalue

defFn rvaluePlace (.plain "rvaluePlace")
  (.plain "Extract the place from an rvalue, if any.")
  (rv "The rvalue." : Rvalue)
  : Option Place where
  | .use o => o·operandPlace
  | .ref _ _ p => Some p

end Rvalue

defEnum Statement (.raw "s", .raw "S")
  "Statements"
  "A MIR statement within a basic block."
where
  | assign (lhs : Place) (rhs : Rvalue)
    "Assign an rvalue to a place."
    (#lhs, .doc (.plain " := "), #rhs)
  | storageLive (lcl : Local)
    "Mark a local's storage as live."
    (.doc (.plain "StorageLive"), .sym .lparen,
     #lcl, .sym .rparen)
  | storageDead (lcl : Local)
    "Mark a local's storage as dead."
    (.doc (.plain "StorageDead"), .sym .lparen,
     #lcl, .sym .rparen)
  deriving Repr, BEq, Hashable

namespace Statement

defFn statementPlaces (.plain "statementPlaces")
  (.plain "Extract all places referenced by a statement.")
  (s "The statement." : Statement)
  : Set Place where
  | .assign lhs rhs =>
      ⦃lhs⦄ ∪ (rhs·rvaluePlace)·toSet
  | .storageLive _ => ∅
  | .storageDead _ => ∅

end Statement

defEnum Terminator (.raw "t",
    .doc (.plain "Term"))
  "Terminators"
  "A basic block terminator."
where
  | goto (target : BasicBlockIdx)
    "Unconditional jump."
    (.doc (.plain "goto "), #target)
  | switchInt (operand : Operand)
    "Switch on an integer value."
    (.doc (.plain "switchInt"), .sym .lparen,
     #operand, .sym .rparen)
  | return_
    "Return from the function."
    (.doc (.plain "return"))
  | unreachable
    "Marks unreachable code."
    (.doc (.plain "unreachable"))
  | drop (place : Place) (target : BasicBlockIdx)
    "Drop the value at a place."
    (.doc (.plain "drop"), .sym .lparen,
     #place, .doc (.plain ", "), #target,
     .sym .rparen)
  | call (callee : Operand) (args : List Operand)
      (targetPlace : Place)
      (nextBlock : BasicBlockIdx)
    "Call a function."
    (#callee, .sym .lparen,
     #args (.raw "\\bar{o}"),
     .sym .rparen, .doc (.plain " → "),
     #targetPlace, .doc (.plain ", "), #nextBlock)
  deriving Repr, BEq, Hashable

namespace Terminator

defFn terminatorPlaces (.plain "terminatorPlaces")
  (.plain "Extract all places referenced by a terminator.")
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

defStruct BasicBlock (.raw "B",
    .doc (.plain "BasicBlock"))
  "Basic Blocks"
  "A basic block: a sequence of statements followed \
   by a terminator."
where
  | statements "The statements in the block."
      : List Statement
  | terminator "The block's terminator." : Terminator
  deriving Repr, BEq, Hashable

namespace BasicBlock

defFn basicBlockPlaces (.plain "basicBlockPlaces")
  (.plain "All places referenced in a basic block.")
  (bb "The basic block." : BasicBlock)
  : Set Place where
  | ⟨stmts, t⟩ =>
      (stmts·setFlatMap fun s => s·statementPlaces) ∪ t·terminatorPlaces

end BasicBlock

defStruct Body (.doc (.plain "body"),
    .doc (.plain "Body"))
  "Bodies"
  "A MIR function body"
where
  | decls "The local variable declarations."
      : List Ty
  | basicBlocks "The basic blocks." : List BasicBlock
  deriving Repr, BEq, Hashable

namespace Body

defFn bodyPlaces (.plain "bodyPlaces")
  (.plain "All places referenced in a function body.")
  (body "The function body." : Body)
  : Set Place where
  | ⟨_, bbs⟩ =>
      bbs·setFlatMap fun bb => bb·basicBlockPlaces

end Body

defStruct PlaceTy (.doc (.plain "pty"),
    .doc (.plain "PlaceTy"))
  "Place Types"
  "The type of a place: a type paired with an optional \
   variant index (set after a downcast)."
where
  | ty "The type." : Ty
  | variant "The variant index, if downcasted."
      : Option VariantIdx
  deriving Repr, BEq, Hashable

defProperty validProjTy (.plain "validProjTy")
  (τDoc, projsDoc) =>
    (.seq [τDoc, .plain " is a valid type for projection list ",
           projsDoc])
  (τ "The current type." : Ty)
  (projs "The projection elements." : List ProjElem)
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

defFn isOwned' (.plain "isOwned'")
  (.seq [.plain "Check whether a place is owned by walking \
    its projection list. Returns ", .code "false",
    .plain " as soon as a dereference of a reference is \
    encountered, ", .code "true", .plain " if all \
    projections are traversed without dereferencing a \
    reference."])
  (τ "The current type." : Ty)
  (projs "The projection elements." : List ProjElem)
  requires validProjTy(τ, projs)
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

defFn placeTy' (.plain "placeTy'")
  (.seq [.plain "Project a type through a list of \
    projection elements. Returns the final ",
    .code "PlaceTy", .plain " after all projections."])
  (τ "The current type." : Ty)
  (v "The variant index." : Option VariantIdx)
  (projs "The projection elements." : List ProjElem)
  requires validProjTy(τ, projs)
  : PlaceTy where
  | τ ; v ; [] => PlaceTy⟨τ, v⟩
  | .ref _ _ pointee ; _ ; .deref :: π =>
      placeTy' ‹pointee, None, π›
  | .box inner ; _ ; .deref :: π =>
      placeTy' ‹inner, None, π›
  | _ ; _ ; (.field _ τ) :: π =>
      placeTy' ‹τ, None, π›
  | .array elem _ ; _ ; (.index _) :: π =>
      placeTy' ‹elem, None, π›
  | τ ; _ ; (.downcast v) :: π =>
      placeTy' ‹τ, Some v, π›

defProperty validPlace (.plain "valid")
  (bodyDoc, pDoc) =>
    (.seq [pDoc, .plain " is a valid place in body ",
           bodyDoc])
  (body "The function body." : Body)
  (p "The place." : Place)
  :=
    p↦base↦index < body↦decls·length ∧
    validProjTy ‹body↦decls ! p↦base↦index, p↦projection›

defProperty validBody (.plain "validBody")
  (bodyDoc) =>
    (.seq [bodyDoc, .plain " is valid"])
  (body "The function body." : Body)
  where
    | body =>
        body·bodyPlaces·forAll fun p => validPlace ‹body, p›

defFn placeTy (.plain "ty")
  (.seq [.plain "Compute the type of a place: look up the \
    base local in ", .math (.raw "\\Delta"),
    .plain ", then project through projections."])
  (body "The function body." : Body)
  (place "The place to type-check." : Place)
  requires validPlace(body, place)
  : PlaceTy :=
    placeTy' ‹body↦decls ! place↦base↦index, None, place↦projection, lean_proof("h_validPlace.2")›

defFn isOwned (.plain "isOwned")
  (.seq [.plain "Returns ", .code "true",
    .plain " iff a place is owned, i.e. it does not project \
    from the dereference of a reference-typed place. See ",
    .code "definitions/places.md", .plain "."])
  (body "The function body." : Body)
  (place "The place to type-check." : Place)
  requires validPlace(body, place)
  : Bool :=
    isOwned' ‹body↦decls ! place↦base↦index, place↦projection, lean_proof("h_validPlace.2")›
