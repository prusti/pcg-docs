import MIR.IsSized
import MIR.Place
import MIR.ConstValue
import MIR.Statements
import Core.Dsl.DefFn
import Core.Dsl.DefProperty

defStruct BasicBlockIdx (.text "bb",
    .text "BasicBlockIdx")
  "Basic Block Indices"
  (.plain "An index into the list of basic blocks.")
where
  | index "The basic block index." : Nat

defStruct Location (.raw "\\ell", .text "Location")
  "Locations"
  (.plain "A location in the MIR, identifying a statement \
   within a basic block.")
where
  | block "The basic block." : BasicBlockIdx
  | stmtIdx "The statement index within the block." : Nat

defEnum Terminator (.raw "t",
    .text "Term")
  "Terminators"
  (.plain "A basic block terminator.")
where
  | goto (target : BasicBlockIdx)
    "Unconditional jump."
  | switchInt (operand : Operand)
      (cases : List (IntValue × BasicBlockIdx))
      (fallback : BasicBlockIdx)
    "Switch on an integer value: jump to the case-matching \
     block, or to `fallback` when no case matches. The cases \
     are a list of `(value, target)` pairs scanned in order \
     for the first match."
  | return_
    "Return from the function."
    (.text "return")
  | unreachable
    "Marks unreachable code."
  | drop (place : Place) (target : BasicBlockIdx)
    "Drop the value at a place."
  | call (callee : Operand) (args : List Operand)
      (targetPlace : Place)
      (nextBlock : BasicBlockIdx)
    "Call a function."
    (#callee, .sym .lparen,
     #args (.raw "\\bar{o}"),
     .sym .rparen, .text " → ",
     #targetPlace, .text ", ", #nextBlock)
  deriving Repr, BEq, Hashable

instance : Inhabited Terminator where
  default := .unreachable

namespace Terminator

defFn terminatorPlaces (.plain "terminatorPlaces")
  (.plain "Extract all places referenced by a terminator.")
  (t "The terminator." : Terminator)
  : Set Place where
  | .goto _ => ∅
  | .switchInt o _ _ => o·operandPlace·toSet
  | .return_ => ∅
  | .unreachable => ∅
  | .drop p _ => ⦃p⦄
  | .call callee args dest _ =>
      ⦃dest⦄ ∪ callee·operandPlace·toSet ∪ (args·setFlatMap fun a => a·operandPlace·toSet)

end Terminator

defStruct BasicBlock (.raw "B",
    .text "BasicBlock")
  "Basic Blocks"
  (.plain "A basic block: a sequence of statements followed \
   by a terminator.")
where
  | statements "The statements in the block."
      : List Statement
  | terminator "The block's terminator." : Terminator
  deriving Repr, BEq, Hashable, Inhabited

namespace BasicBlock

defFn basicBlockPlaces (.plain "basicBlockPlaces")
  (.plain "All places referenced in a basic block.")
  (bb "The basic block." : BasicBlock)
  : Set Place :=
    (bb↦statements·setFlatMap fun s => s·statementPlaces) ∪
      bb↦terminator·terminatorPlaces

end BasicBlock

defStruct Body (.text "body",
    .text "Body")
  "Bodies"
  (.plain "A MIR function body.")
where
  | decls "The local variable declarations." : List Ty
  | numArgs "The number of arguments" : Nat
  | blocks "The basic blocks." : List BasicBlock
  deriving Repr, BEq, Hashable, Inhabited

namespace Body

defFn bodyPlaces (.plain "bodyPlaces")
  (.plain "All places referenced in a function body.")
  (body "The function body." : Body)
  : Set Place :=
    body↦blocks·setFlatMap fun bb => bb·basicBlockPlaces

end Body

defStruct PlaceTy (.text "pty",
    .text "PlaceTy")
  "Place Types"
  (.plain "The type of a place: a type paired with an optional \
   variant index (set after a downcast).")
where
  | ty "The type." : Ty
  | variant "The variant index, if downcasted."
      : Option VariantIdx
  deriving Repr, BEq, Hashable

defProperty validProjTy (.plain "validProjTy")
  short (τDoc, projsDoc) =>
    (.seq [τDoc, .plain " is a valid type for projection list ",
           projsDoc])
  long (τDoc, projsDoc) =>
    (.seq [.plain "every projection step in ", projsDoc,
           .plain " is well-typed when applied to ", τDoc,
           .plain ": a ", .code ".deref",
           .plain " step requires a reference or ",
           .code "Box", .plain ", a ", .code ".field",
           .plain " step lands in any type, an ",
           .code ".index",
           .plain " step requires an array, and a ",
           .code ".downcast",
           .plain " step lands in any type"])
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
  short (bodyDoc, pDoc) =>
    (.seq [pDoc, .plain " is a valid place in body ",
           bodyDoc])
  long (bodyDoc, pDoc) =>
    (.seq [.plain "the base local of ", pDoc,
           .plain " is in range of ", bodyDoc,
           .plain "'s declarations, and the projection list \
           of ", pDoc,
           .plain " is well-typed against the type of that \
           local"])
  (body "The function body." : Body)
  (p "The place." : Place)
  :=
    p↦«local»↦index < body↦decls·length ∧
    validProjTy ‹body↦decls ! p↦«local»↦index, p↦projection›

defProperty validLocation (.plain "validLocation")
  short (bodyDoc, locDoc) =>
    (.seq [locDoc, .plain " is a valid location in body ",
           bodyDoc])
  long (bodyDoc, locDoc) =>
    (.seq [.plain "the block index of ", locDoc,
           .plain " is in range of ", bodyDoc,
           .plain "'s blocks, and the statement index of ",
           locDoc,
           .plain " is at most the number of statements in \
           that block (so the terminator position is \
           included)"])
  (body "The function body." : Body)
  (loc "The location." : Location)
  :=
    loc↦block↦index < body↦blocks·length ∧
    loc↦stmtIdx ≤
      (body↦blocks ! loc↦block↦index)↦statements·length

defProperty validBody (.plain "validBody")
  short (bodyDoc) =>
    (.seq [bodyDoc, .plain " is a valid body"])
  long (bodyDoc) =>
    (.seq [.plain "every place referenced in ", bodyDoc,
           .plain " is a valid place in ", bodyDoc,
           .plain ", and every local declaration of ",
           bodyDoc, .plain " is a sized type"])
  (body "The function body." : Body)
  :=
    (body·bodyPlaces·forAll fun p => validPlace ‹body, p›) ∧
    (body↦decls·forAll fun t => IsSized ‹t›)

defFn placeTy (.plain "ty")
  (.seq [.plain "Compute the type of a place: look up the \
    base local in ", .math (.raw "\\Delta"),
    .plain ", then project through projections."])
  (body "The function body." : Body)
  (place "The place to type-check." : Place)
  requires validPlace(body, place)
  : PlaceTy :=
    placeTy' ‹body↦decls ! place↦«local»↦index, None, place↦projection, lean_proof("h_validPlace.2")›

defFn isOwned (.plain "isOwned")
  (.seq [.plain "Returns ", .code "true",
    .plain " iff a place is owned, i.e. it does not project \
    from the dereference of a reference-typed place. See ",
    .code "definitions/places.md", .plain "."])
  (body "The function body." : Body)
  (place "The place to type-check." : Place)
  requires validPlace(body, place)
  : Bool :=
    isOwned' ‹body↦decls ! place↦«local»↦index, place↦projection, lean_proof("h_validPlace.2")›
