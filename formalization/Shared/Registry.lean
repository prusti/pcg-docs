import Shared.EnumDef
import Shared.StructDef

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

/-- Register an enum definition from the given module. -/
def registerEnumDef
    (e : EnumDef) (mod : Lean.Name) : IO Unit :=
  enumRegistry.modify (· ++ [⟨e, mod⟩])

/-- Register a struct definition from the given module. -/
def registerStructDef
    (s : StructDef) (mod : Lean.Name) : IO Unit :=
  structRegistry.modify (· ++ [⟨s, mod⟩])

/-- Retrieve all registered enum definitions. -/
def getRegisteredEnums : IO (List RegisteredEnum) :=
  enumRegistry.get

/-- Retrieve all registered struct definitions. -/
def getRegisteredStructs : IO (List RegisteredStruct) :=
  structRegistry.get
