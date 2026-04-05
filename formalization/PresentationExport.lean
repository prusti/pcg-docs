import PCG.Presentation
import OpSem

def main (args : List String) : IO Unit := do
  let outPath := args.head? |>.getD
    "generated/presentation.tex"
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
  let doc := Latex.document latexPackages
    latexPreamble body
  IO.FS.writeFile ⟨outPath⟩ (doc.render ++ "\n")
  IO.println s!"  wrote {outPath}"
