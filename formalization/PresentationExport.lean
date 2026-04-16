import PCG.Presentation
import OpSem

/-- Parse a `--key=value` flag from the argument list. -/
private def parseFlag (args : List String)
    (key : String) (default : String) : String :=
  let flagPrefix := s!"--{key}="
  match args.find? (·.startsWith flagPrefix) with
  | some arg => (arg.drop flagPrefix.length).toString
  | none => default

def main (args : List String) : IO Unit := do
  let outPath := args.filter (! ·.startsWith "--")
    |>.head? |>.getD "generated/presentation.tex"
  let makePdf := parseFlag args "make-pdf" "true" == "true"
  let dir := System.FilePath.mk outPath |>.parent
    |>.getD (System.FilePath.mk ".")
  IO.FS.createDirAll dir
  let descrs ← getRegisteredDescrs
  let enums ← getRegisteredEnums
  let structs ← getRegisteredStructs
  let orders ← getRegisteredOrders
  let fns ← getRegisteredFns
  let props ← getRegisteredProperties
  let body := buildPresentationLatex
    descrs enums structs orders fns props
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
    let auxExts := ["aux", "log", "fls",
                    "fdb_latexmk", "out"]
    for ext in auxExts do
      let p := dir / s!"{stem}.{ext}"
      try IO.FS.removeFile p catch | _ => pure ()
    let pdfPath := dir / s!"{stem}.pdf"
    IO.println s!"  wrote {pdfPath}"
