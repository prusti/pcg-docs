import Core.Doc
import Core.Dsl.Types.Feature

/-- A single element of a template `Presentation`: either
    free-form prose or a reference to a registered DSL
    definition (struct, enum, alias, function, property,
    inductive property, or theorem) by short name.

    A `defRef "Place"` resolves at render time to the
    registered definition with that name; if no such name
    exists, the presentation export aborts. -/
inductive PresElement where
  /-- Free-form prose, rendered in place. -/
  | doc (d : Doc)
  /-- Reference to a registered definition by short name
      (e.g. `"Place"`). -/
  | defRef (name : String)
  deriving Repr

/-- A user-defined "template" presentation: a curated subset
    of registered DSL definitions, interleaved with prose,
    rendered to its own PDF.

    Any registered definition that is transitively referenced
    by an embedded one but not itself listed in `elems` is
    rendered in an "Appendix" section so the resulting PDF is
    self-contained. -/
structure Presentation where
  /-- Body content, rendered top-to-bottom. New templates
      should usually build this with the `presBody!` macro
      (see `Core/Doc/PresInterp.lean`), which lets the body be
      written as a markdown-like interpolated string. -/
  elems : List PresElement
  /-- Output filename stem (without extension). The presentation
      exporter writes `<filename>.tex` and `<filename>.pdf`
      next to the full presentation. -/
  filename : String
  /-- Optional document title, rendered via `\title{…}` /
      `\maketitle`. Empty disables the title block. -/
  title : String := ""
  /-- Features disabled in this presentation. Variants and
      match arms tagged with any of these features are
      omitted from the LaTeX rendering. Empty (the default)
      means every feature is enabled — the rendering matches
      the source DSL exactly. -/
  disabledFeatures : List Feature := []
  deriving Repr

namespace PresElement

/-- Extract the referenced name from a `defRef`, or `none`
    for `doc` elements. -/
def defRef? : PresElement → Option String
  | .defRef n => some n
  | .doc _ => none

end PresElement
