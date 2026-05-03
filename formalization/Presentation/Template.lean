import Presentation
import Core.Export.Lean

/-! # Template presentations

A "template" presentation lets a user assemble a small, focused
PDF that contains only chosen registered DSL definitions
interleaved with prose. Any registered definition transitively
referenced by an embedded one but not itself listed in the
template's `elems` is rendered in an "Appendix" section so the
resulting PDF is self-contained.

The user-facing data type is `Presentation` (see
`Core/Dsl/Types/PresentationDef.lean`); template values are
registered via `registerPresentationDef`. The presentation
exporter walks `Registry.presentations` and calls
`buildTemplatePresentationLatex` once per entry, producing
`<filename>.pdf` next to the full presentation. -/

/-- The kind of registered definition a name resolves to.
    `Order`s are not addressable by name — they tag along with
    their enum and so are not represented here. -/
inductive DepKind where
  | struct
  | enum_
  | alias
  | fn
  | property
  | inductiveProperty
  | theorem_
  deriving Repr, BEq

namespace Registry

/-- The set of "primitive" type names that should never count
    as registered dependencies. These are emitted by the type
    machinery (e.g. `DSLType.toLean`) but have no `defStruct` /
    `defEnum` of their own. -/
private def primitiveTypeNames : List String :=
  ["Nat", "String", "Bool", "Unit", "UInt8", "UInt16", "UInt32",
   "UInt64", "USize", "Option", "List", "Set", "Map"]

/-- Look up the kind a registered name belongs to, if any. -/
def lookupKind (reg : Registry) (n : String) : Option DepKind :=
  if reg.structs.any (·.structDef.name == n) then some .struct
  else if reg.enums.any (·.enumDef.name.name == n) then some .enum_
  else if reg.aliases.any (·.aliasDef.name == n) then some .alias
  else if reg.fns.any (·.fnDef.name == n) then some .fn
  else if reg.properties.any (·.propertyDef.fnDef.name == n) then
    some .property
  else if reg.inductiveProperties.any
      (·.inductivePropertyDef.name == n) then
    some .inductiveProperty
  else if reg.theorems.any (·.theoremDef.name == n) then
    some .theorem_
  else none

/-- All registered names this name depends on, dispatched by
    kind. Returns `[]` for unknown / primitive names. -/
def dependenciesOf (reg : Registry) (n : String) : List String :=
  match reg.lookupKind n with
  | some .struct =>
    (reg.structs.find? (·.structDef.name == n)).map
      (·.structDef.referencedTypes) |>.getD []
  | some .enum_ =>
    (reg.enums.find? (·.enumDef.name.name == n)).map
      (·.enumDef.referencedTypes) |>.getD []
  | some .alias =>
    (reg.aliases.find? (·.aliasDef.name == n)).map
      (·.aliasDef.referencedTypes) |>.getD []
  | some .fn =>
    (reg.fns.find? (·.fnDef.name == n)).map
      (·.fnDef.referencedNames) |>.getD []
  | some .property =>
    (reg.properties.find? (·.propertyDef.fnDef.name == n)).map
      (·.propertyDef.referencedNames) |>.getD []
  | some .inductiveProperty =>
    (reg.inductiveProperties.find?
        (·.inductivePropertyDef.name == n)).map
      (·.inductivePropertyDef.referencedNames) |>.getD []
  | some .theorem_ =>
    (reg.theorems.find? (·.theoremDef.name == n)).map
      (·.theoremDef.referencedNames) |>.getD []
  | none => []

/-- Whether `n` resolves to a registered definition. Primitive
    type names (`Nat`, `Option`, `Set`, …) and unknown names
    return `false`. -/
def isRegistered (reg : Registry) (n : String) : Bool :=
  reg.lookupKind n |>.isSome

/-- DFS closure over the registered-dependency graph from
    `seeds`. Returns every reachable registered name in
    discovery order, deduplicated. Names that don't resolve
    to a registered definition (primitives or unknowns) are
    silently skipped — callers that want to surface those as
    errors should walk separately via `unresolvedReferences`. -/
partial def closure
    (reg : Registry) (seeds : List String) : List String :=
  let rec go (acc : List String)
      : List String → List String
    | [] => acc
    | n :: rest =>
      if acc.contains n then go acc rest
      else if !reg.isRegistered n then go acc rest
      else
        let deps := reg.dependenciesOf n
        go (acc ++ [n]) (deps ++ rest)
  go [] seeds

/-- Collect every name reachable from `seeds` (transitively
    through the registered-dependency graph) that does *not*
    resolve to a registered definition and is not a built-in
    primitive type. These are typically free variables /
    locals captured by the lightweight `referencedNames`
    walker, or genuine typos. The exporter surfaces them as
    a warning so users can audit a template's surface area. -/
partial def unresolvedReferences
    (reg : Registry) (seeds : List String) : List String :=
  let rec go (visited unresolved : List String)
      : List String → List String × List String
    | [] => (visited, unresolved)
    | n :: rest =>
      if visited.contains n then go visited unresolved rest
      else if reg.isRegistered n then
        let deps := reg.dependenciesOf n
        go (visited ++ [n]) unresolved (deps ++ rest)
      else if primitiveTypeNames.contains n
              || unresolved.contains n then
        go visited unresolved rest
      else go visited (unresolved ++ [n]) rest
  (go [] [] seeds).snd

/-- Keep only registered items whose name is in `names`. The
    `descrs` and `presentations` lists are dropped (they have
    no name to filter on). `orders` come along when their
    enum is included. -/
def restrictToNames
    (reg : Registry) (names : List String) : Registry :=
  let keepEnum (e : RegisteredEnum) : Bool :=
    names.contains e.enumDef.name.name
  let keepEnums := reg.enums.filter keepEnum
  let keptEnumNames := keepEnums.map (·.enumDef.name.name)
  { descrs := []
    enums := keepEnums
    structs := reg.structs.filter
      fun s => names.contains s.structDef.name
    aliases := reg.aliases.filter
      fun a => names.contains a.aliasDef.name
    orders := reg.orders.filter
      fun o => keptEnumNames.contains o.enumName
    fns := reg.fns.filter
      fun f => names.contains f.fnDef.name
    properties := reg.properties.filter
      fun p => names.contains p.propertyDef.fnDef.name
    inductiveProperties := reg.inductiveProperties.filter
      fun p => names.contains p.inductivePropertyDef.name
    theorems := reg.theorems.filter
      fun t => names.contains t.theoremDef.name
    presentations := [] }

end Registry

/-- A failure to render a template presentation: one or more
    `defRef` names did not resolve to any registered
    definition. The exporter renders these as a hard error
    rather than emitting a partial PDF. -/
structure TemplateError where
  /-- Names listed via `.defRef` that are not registered. -/
  unresolvedDefRefs : List String
  /-- Names reachable from the closure that did not resolve
      (informational; most are free variables in DSL bodies
      and not typically actionable). -/
  unresolvedReferences : List String
  deriving Repr

namespace TemplateError

/-- Whether the error has any unresolved `defRef`s — the
    only condition that aborts the export. Informational
    `unresolvedReferences` are reported as warnings. -/
def isFatal (e : TemplateError) : Bool :=
  !e.unresolvedDefRefs.isEmpty

/-- A short human-readable summary of the unresolved names. -/
def message (e : TemplateError) : String :=
  let refs := String.intercalate ", " e.unresolvedDefRefs
  s!"unresolved defRef name(s): {refs}"

end TemplateError

/-- Render a single `PresElement` to LaTeX, using the same
    per-kind helpers as the full presentation. A `defRef`
    builds a one-element sub-registry on the fly so it
    flows through `renderRegistryItems` like any other slice. -/
private def renderElement
    (reg : Registry) (ctx : RenderCtx) : PresElement → Latex
  | .doc d => Latex.seq [d.toLatex, .newline, .newline]
  | .defRef n =>
    renderRegistryItems (reg.restrictToNames [n]) ctx

/-- Order names by kind in the same sequence
    `renderRegistryItems` uses, so the appendix layout
    mirrors the body. Within each kind, original
    registration order is preserved (since `restrictToNames`
    filters but does not reorder its source lists). -/
private def appendixSortByKind
    (reg : Registry) (names : List String) : List String :=
  let isKind (k : DepKind) (n : String) : Bool :=
    reg.lookupKind n == some k
  let kinds : List DepKind :=
    [.struct, .alias, .enum_, .inductiveProperty, .fn,
     .property, .theorem_]
  kinds.flatMap fun k => names.filter (isKind k)

/-- Build the full LaTeX body for a template presentation.
    Returns `Except` so the exporter can surface unresolved
    `defRef` names as a hard error rather than silently
    emitting a half-broken PDF. -/
def buildTemplatePresentationLatex
    (reg : Registry) (p : Presentation)
    : Except TemplateError Latex := Id.run do
  let included : List String := p.elems.filterMap PresElement.defRef?
  let unresolvedDefRefs : List String :=
    included.filter (fun n => !reg.isRegistered n)
  if !unresolvedDefRefs.isEmpty then
    return .error
      { unresolvedDefRefs := unresolvedDefRefs
        unresolvedReferences := [] }
  let closed : List String := reg.closure included
  let appendixNames : List String :=
    appendixSortByKind reg
      (closed.filter (fun n => !included.contains n))
  let subReg : Registry := reg.restrictToNames closed
  let ctx : RenderCtx := mkRenderCtx subReg p.disabledFeatures
  let titleBlock : Latex :=
    if p.title.isEmpty then .seq []
    else .seq [
      .cmd "title" [.text p.title], .newline,
      .cmd0 "maketitle", .newline ]
  let body : List Latex :=
    p.elems.map (renderElement subReg ctx)
  let appendixBlock : Latex :=
    if appendixNames.isEmpty then .seq []
    else
      let appendixReg := subReg.restrictToNames appendixNames
      .seq [
        .cmd "section*" [.text "Appendix"], .newline,
        renderRegistryItems appendixReg ctx ]
  -- Trailing `.newline`s after `\tableofcontents` / `\newpage`
  -- give TeX a token boundary so the first body element
  -- (typically prose starting with a letter) is not glued
  -- onto `\newpage` to form an undefined macro.
  return .ok (.seq
    ([titleBlock, .tableofcontents, .newline,
      .newpage, .newline] ++ body
      ++ [appendixBlock]))
