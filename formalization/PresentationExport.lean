import Presentation
import Presentation.Template
import Presentation.Templates.Louis
import OpSem
-- `Properties` is its own library bridging `PCG` and `OpSem`,
-- opt-in so the Rust exporter's import chain stays untouched.
-- The presentation export wants the soundness and aliasing
-- statements rendered, so we pull it in explicitly.
import Properties

/-- Parse a `--key=value` flag from the argument list. -/
private def parseFlag (args : List String)
    (key : String) (default : String) : String :=
  let flagPrefix := s!"--{key}="
  match args.find? (·.startsWith flagPrefix) with
  | some arg => (arg.drop flagPrefix.length).toString
  | none => default

/-- Run `latexmk` on `texPath` (whose parent is `dir`) and
    delete the standard auxiliary outputs on success. Shared
    between the full presentation and each template
    presentation so they handle aux-file cleanup the same way. -/
private def runLatexmk
    (dir : System.FilePath) (texPath : System.FilePath)
    : IO Unit := do
  let texName := texPath.fileName.getD "presentation.tex"
  let proc ← IO.Process.spawn {
    cmd := "latexmk"
    args := #["-pdf", "-interaction=nonstopmode",
              "-halt-on-error", texName]
    cwd := dir
  }
  let exitCode ← proc.wait
  if exitCode != 0 then
    throw (IO.userError
      s!"latexmk failed for {texPath} with exit code {exitCode}")
  let stem := texPath.fileStem.getD "presentation"
  let auxExts := ["aux", "log", "fls", "fdb_latexmk", "out"]
  for ext in auxExts do
    let p := dir / s!"{stem}.{ext}"
    try IO.FS.removeFile p catch | _ => pure ()
  let pdfPath := dir / s!"{stem}.pdf"
  IO.println s!"  wrote {pdfPath}"

def main (args : List String) : IO Unit := do
  let outPath := args.filter (! ·.startsWith "--")
    |>.head? |>.getD "generated/presentation.tex"
  let makePdf := parseFlag args "make-pdf" "true" == "true"
  let dir := System.FilePath.mk outPath |>.parent
    |>.getD (System.FilePath.mk ".")
  IO.FS.createDirAll dir
  let reg ← Registry.current
  let body := buildPresentationLatex reg
  let doc := Latex.document latexPackages
    latexPreamble body
  IO.FS.writeFile ⟨outPath⟩ (doc.render ++ "\n")
  IO.println s!"  wrote {outPath}"
  if makePdf then
    runLatexmk dir (System.FilePath.mk outPath)
  for t in reg.presentations do
    let p := t.presentation
    match buildTemplatePresentationLatex reg p with
    | .error err =>
      throw (IO.userError
        s!"template '{p.filename}': {err.message}")
    | .ok templateBody =>
      let tDoc := Latex.document latexPackages latexPreamble
        templateBody
      let tTexPath := dir / s!"{p.filename}.tex"
      IO.FS.writeFile tTexPath (tDoc.render ++ "\n")
      IO.println s!"  wrote {tTexPath}"
      if makePdf then
        runLatexmk dir tTexPath
