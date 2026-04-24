import Core.Dsl.Types.AliasDef
import Core.Dsl.Types.EnumDef
import Core.Dsl.Types.StructDef
import Core.Dsl.Types.OrderDef
import Core.Dsl.Types.FnDef
import Core.Dsl.Types.PropertyDef
import Core.Dsl.Types.InductivePropertyDef

/-- A registered enum definition with its source module. -/
structure RegisteredEnum where
  /-- The enum definition. -/
  enumDef : EnumDef
  /-- The Lean module where this enum was defined. -/
  leanModule : Lean.Name
  deriving Repr

/-- A registered struct definition with its source module. -/
structure RegisteredStruct where
  /-- The struct definition. -/
  structDef : StructDef
  /-- The Lean module where this struct was defined. -/
  leanModule : Lean.Name
  deriving Repr

/-- Global registry of all `defEnum`-defined types. -/
initialize enumRegistry : IO.Ref (List RegisteredEnum) ←
  IO.mkRef []

/-- Global registry of all `defStruct`-defined types. -/
initialize structRegistry : IO.Ref (List RegisteredStruct) ←
  IO.mkRef []

/-- Generic-type names whose type parameters must carry
    `BEq` and `Hashable` instances (directly, because a field
    or variant uses `Map` / `Set`, or transitively, because a
    field or variant references another type already in this
    list). Populated by `defStruct` / `defEnum` when they
    detect such usage, and read by both commands when
    deciding whether a new generic type's fields drag in
    those constraints. -/
initialize hashPropagatingTypes : IO.Ref (List String) ←
  IO.mkRef []

/-- Record that `name` is a generic type whose parameters
    must carry `BEq` and `Hashable` constraints. Idempotent. -/
def registerHashPropagating (name : String) : IO Unit := do
  let cur ← hashPropagatingTypes.get
  unless cur.contains name do
    hashPropagatingTypes.set (cur ++ [name])

/-- Registry mapping symbol strings to the type name that
    claimed them, for duplicate detection. -/
initialize symbolRegistry :
    IO.Ref (List (String × String)) ←
  IO.mkRef []

/-- Check that a symbol is not already claimed by another
    type. Logs a warning if a duplicate is found. -/
private def checkSymbolUnique
    (sym : MathDoc) (typeName : String) : IO Unit := do
  let rendered := sym.toLatexMath.render
  if rendered.isEmpty then return
  let existing ← symbolRegistry.get
  match existing.find? (·.1 == rendered) with
  | some (_, owner) =>
    IO.eprintln s!"warning: symbol '{rendered}' is \
      used by both '{owner}' and '{typeName}'"
  | none => pure ()
  symbolRegistry.modify (· ++ [(rendered, typeName)])

/-- Register an enum definition from the given module. -/
def registerEnumDef
    (e : EnumDef) (mod : Lean.Name) : IO Unit := do
  checkSymbolUnique e.symbolDoc e.name.name
  checkSymbolUnique e.setDoc e.name.name
  enumRegistry.modify (· ++ [⟨e, mod⟩])

/-- Register a struct definition from the given module. -/
def registerStructDef
    (s : StructDef) (mod : Lean.Name) : IO Unit := do
  checkSymbolUnique s.symbolDoc s.name
  checkSymbolUnique s.setDoc s.name
  structRegistry.modify (· ++ [⟨s, mod⟩])

/-- Retrieve all registered enum definitions. -/
def getRegisteredEnums : IO (List RegisteredEnum) :=
  enumRegistry.get

/-- Retrieve all registered struct definitions. -/
def getRegisteredStructs : IO (List RegisteredStruct) :=
  structRegistry.get

/-- A registered type-alias definition with its source module. -/
structure RegisteredAlias where
  /-- The alias definition. -/
  aliasDef : AliasDef
  /-- The Lean module where this alias was defined. -/
  leanModule : Lean.Name
  deriving Repr

/-- Global registry of all `defAlias`-defined type aliases. -/
initialize aliasRegistry : IO.Ref (List RegisteredAlias) ←
  IO.mkRef []

/-- Register a type-alias definition from the given module. -/
def registerAliasDef
    (a : AliasDef) (mod : Lean.Name) : IO Unit := do
  checkSymbolUnique a.symbolDoc a.name
  checkSymbolUnique a.setDoc a.name
  aliasRegistry.modify (· ++ [⟨a, mod⟩])

/-- Retrieve all registered type-alias definitions. -/
def getRegisteredAliases : IO (List RegisteredAlias) :=
  aliasRegistry.get

/-- A registered order definition with its source module. -/
structure RegisteredOrder where
  /-- The order definition. -/
  orderDef : OrderDef
  /-- The enum name this order is defined on. -/
  enumName : String
  /-- The Lean module where this order was defined. -/
  leanModule : Lean.Name
  deriving Repr

/-- Global registry of all `defOrder`-defined orderings. -/
initialize orderRegistry : IO.Ref (List RegisteredOrder) ←
  IO.mkRef []

/-- Register an order definition. -/
def registerOrderDef
    (o : OrderDef) (mod : Lean.Name) : IO Unit :=
  orderRegistry.modify
    (· ++ [⟨o, o.enumName, mod⟩])

/-- Retrieve all registered order definitions. -/
def getRegisteredOrders : IO (List RegisteredOrder) :=
  orderRegistry.get

/-- A registered function definition with its source module. -/
structure RegisteredFn where
  /-- The function definition. -/
  fnDef : FnDef
  /-- The Lean module where this function was defined. -/
  leanModule : Lean.Name
  deriving Repr

/-- Global registry of all `defFn`-defined functions. -/
initialize fnRegistry : IO.Ref (List RegisteredFn) ←
  IO.mkRef []

/-- Register a function definition. -/
def registerFnDef
    (f : FnDef) (mod : Lean.Name) : IO Unit :=
  fnRegistry.modify (· ++ [⟨f, mod⟩])

/-- Retrieve all registered function definitions. -/
def getRegisteredFns : IO (List RegisteredFn) :=
  fnRegistry.get

/-- A registered property definition with its source
    module. -/
structure RegisteredProperty where
  /-- The property definition. -/
  propertyDef : PropertyDef
  /-- The Lean module where this property was defined. -/
  leanModule : Lean.Name

/-- Global registry of all `defProperty`-defined
    predicates. -/
initialize propertyRegistry :
    IO.Ref (List RegisteredProperty) ←
  IO.mkRef []

/-- Register a property definition. -/
def registerPropertyDef
    (p : PropertyDef) (mod : Lean.Name) : IO Unit :=
  propertyRegistry.modify (· ++ [⟨p, mod⟩])

/-- Retrieve all registered property definitions. -/
def getRegisteredProperties :
    IO (List RegisteredProperty) :=
  propertyRegistry.get

/-- A registered description: free-form `Doc` prose
    attached to a module, rendered in the presentation
    at the point where it was registered. -/
structure RegisteredDescr where
  /-- The description content. -/
  doc : Doc
  /-- The Lean module where this description was
      registered. -/
  leanModule : Lean.Name
  deriving Repr

/-- Global registry of all `descr`-registered
    descriptions. -/
initialize descrRegistry :
    IO.Ref (List RegisteredDescr) ←
  IO.mkRef []

/-- Register a description from the given module. -/
def registerDescr
    (d : Doc) (mod : Lean.Name) : IO Unit :=
  descrRegistry.modify (· ++ [⟨d, mod⟩])

/-- Retrieve all registered descriptions. -/
def getRegisteredDescrs :
    IO (List RegisteredDescr) :=
  descrRegistry.get

/-- A registered inductive-property definition with its source
    module. -/
structure RegisteredInductiveProperty where
  /-- The inductive property definition. -/
  inductivePropertyDef : InductivePropertyDef
  /-- The Lean module where this inductive property was
      defined. -/
  leanModule : Lean.Name
  deriving Repr

/-- Global registry of all `defInductiveProperty`-defined
    predicates. -/
initialize inductivePropertyRegistry :
    IO.Ref (List RegisteredInductiveProperty) ←
  IO.mkRef []

/-- Register an inductive-property definition. -/
def registerInductivePropertyDef
    (p : InductivePropertyDef) (mod : Lean.Name) : IO Unit := do
  checkSymbolUnique p.symbolDoc p.name
  checkSymbolUnique p.setDoc p.name
  inductivePropertyRegistry.modify (· ++ [⟨p, mod⟩])

/-- Retrieve all registered inductive-property definitions. -/
def getRegisteredInductiveProperties :
    IO (List RegisteredInductiveProperty) :=
  inductivePropertyRegistry.get

/-- A snapshot of every kind of registered DSL definition.

    Grouping the registry lists lets downstream consumers
    (presentation, exporters) take a single `Registry` argument
    rather than a long positional list. -/
structure Registry where
  descrs : List RegisteredDescr
  enums : List RegisteredEnum
  structs : List RegisteredStruct
  aliases : List RegisteredAlias
  orders : List RegisteredOrder
  fns : List RegisteredFn
  properties : List RegisteredProperty
  inductiveProperties : List RegisteredInductiveProperty

namespace Registry

/-- Collect a full `Registry` from the current global state. -/
def current : IO Registry := do
  return {
    descrs := ← getRegisteredDescrs
    enums := ← getRegisteredEnums
    structs := ← getRegisteredStructs
    aliases := ← getRegisteredAliases
    orders := ← getRegisteredOrders
    fns := ← getRegisteredFns
    properties := ← getRegisteredProperties
    inductiveProperties := ← getRegisteredInductiveProperties
  }

end Registry
