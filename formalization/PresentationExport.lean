import PCG.Presentation

def main (args : List String) : IO Unit := do
  let outPath := args.head? |>.getD "generated/presentation.tex"
  let dir := System.FilePath.mk outPath |>.parent
    |>.getD (System.FilePath.mk ".")
  IO.FS.createDirAll dir
  let content := presentation.toStandaloneLatex latexPackages
  IO.FS.writeFile ⟨outPath⟩ content
  IO.println s!"  wrote {outPath}"
