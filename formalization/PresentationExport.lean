import PCG.Presentation

def main (args : List String) : IO Unit := do
  let outPath := args.head? |>.getD "generated/presentation.tex"
  let dir := System.FilePath.mk outPath |>.parent
    |>.getD (System.FilePath.mk ".")
  IO.FS.createDirAll dir
  let enums ← getRegisteredEnums
  let structs ← getRegisteredStructs
  let orders ← getRegisteredOrders
  let fns ← getRegisteredFns
  let props ← getRegisteredProperties
  let body := buildPresentationLatex
    enums structs orders fns props
  let pkgLines := latexPackages.map fun p =>
    s!"\\usepackage\{{p}}"
  let lb := "{"
  let rb := "}"
  let content := s!"\\documentclass{lb}article{rb}\n\
    {"\n".intercalate pkgLines}\n\
    {latexPreamble}\n\
    \\begin{lb}document{rb}\n\n\
    {body}\n\n\
    \\end{lb}document{rb}\n"
  IO.FS.writeFile ⟨outPath⟩ content
  IO.println s!"  wrote {outPath}"
