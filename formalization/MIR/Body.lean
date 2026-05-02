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
    "Call a function: the callee operand evaluates to a \
     function pointer (`Value.fnPtr name`) which names a \
     function in the program's function map."
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
  short
    (doc! "{τ} is a valid type for projection list {projs}")
  long
    (doc! "every projection step in {projs} is well-typed when \
      applied to {τ}: a `.deref` step requires a reference or \
      `Box`, a `.field` step lands in any type, an `.index` \
      step requires an array, and a `.downcast` step lands in \
      any type")
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
  (doc! "Check whether a place is owned by walking its projection list. Returns `false` as soon as \
    a dereference of a reference is encountered, `true` if all projections are traversed without \
    dereferencing a reference.")
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
  (doc! "Project a type through a list of projection elements. Returns the final #PlaceTy after all \
    projections.")
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
  short
    (doc! "{p} is a valid place in body {body}")
  long
    (doc! "the base local of {p} is in range of {body}'s \
      declarations, and the projection list of {p} is \
      well-typed against the type of that local")
  (body "The function body." : Body)
  (p "The place." : Place)
  :=
    p↦«local»↦index < body↦decls·length ∧
    validProjTy ‹body↦decls ! p↦«local»↦index, p↦projection›

defProperty validLocation (.plain "validLocation")
  short
    (doc! "{loc} is a valid location in body {body}")
  long
    (doc! "the block index of {loc} is in range of {body}'s \
      blocks, and the statement index of {loc} is at most \
      the number of statements in that block (so the \
      terminator position is included)")
  (body "The function body." : Body)
  (loc "The location." : Location)
  :=
    loc↦block↦index < body↦blocks·length ∧
    loc↦stmtIdx ≤
      (body↦blocks ! loc↦block↦index)↦statements·length

defProperty validBody (.plain "validBody")
  short
    (doc! "{body} is a valid body")
  long
    (doc! "every place referenced in {body} is a valid place \
      in {body}, and every local declaration of {body} is a \
      sized type")
  (body "The function body." : Body)
  :=
    (body·bodyPlaces·forAll fun p => validPlace ‹body, p›) ∧
    (body↦decls·forAll fun t => IsSized ‹t›)

defFn placeTy (.plain "ty")
  (doc! "Compute the type of a place: look up the base local \
    in $\\Delta$, then project through projections.")
  (body "The function body." : Body)
  (place "The place to type-check." : Place)
  requires validPlace(body, place)
  : PlaceTy :=
    placeTy' ‹body↦decls ! place↦«local»↦index, None, place↦projection, lean_proof("h_validPlace.2")›

defFn isOwned (.plain "isOwned")
  (doc! "Returns `true` iff a place is owned, i.e. it does not project from the dereference of a \
    reference-typed place. See `definitions/places.md`.")
  (body "The function body." : Body)
  (place "The place to type-check." : Place)
  requires validPlace(body, place)
  : Bool :=
    isOwned' ‹body↦decls ! place↦«local»↦index, place↦projection, lean_proof("h_validPlace.2")›
