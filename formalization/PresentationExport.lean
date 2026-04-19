import Presentation
import OpSem

/-- Parse a `--key=value` flag from the argument list. -/
private def parseFlag (args : List String)
    (key : String) (default : String) : String :=
  let flagPrefix := s!"--{key}="
  match args.find? (·.startsWith flagPrefix) with
  | some arg => (arg.drop flagPrefix.length).toString
  | none => default

/-- Extract the lines of the LaTeX log that report an
    overfull `\hbox` (each starts with `Overfull \hbox`). -/
private def overfullHboxLines (log : String) : List String :=
  log.splitOn "\n" |>.filter (·.startsWith "Overfull \\hbox")

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
    let texPath := System.FilePath.mk outPath
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
        s!"latexmk failed with exit code {exitCode}")
    let stem := texPath.fileStem.getD "presentation"
    -- Fail the build if the LaTeX log reports any overfull
    -- `\hbox`. Poorly-formatted output (text bleeding into
    -- the margin) is a regression we want CI to catch.
    let logPath := dir / s!"{stem}.log"
    let log ← IO.FS.readFile logPath
    let overfulls := overfullHboxLines log
    let auxExts := ["aux", "log", "fls",
                    "fdb_latexmk", "out"]
    for ext in auxExts do
      let p := dir / s!"{stem}.{ext}"
      try IO.FS.removeFile p catch | _ => pure ()
    unless overfulls.isEmpty do
      throw (IO.userError
        s!"latexmk produced {overfulls.length} overfull \\hbox \
          warnings:\n{"\n".intercalate overfulls}")
    let pdfPath := dir / s!"{stem}.pdf"
    IO.println s!"  wrote {pdfPath}"
