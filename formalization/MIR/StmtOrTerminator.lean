import Core.Dsl.DefEnum
import Core.Dsl.DefFn
import MIR.Body

defEnum StmtOrTerminator
    (.raw "sot", .text "StmtOrTerminator")
  "Statements or Terminators"
  (doc! "A statement-or-terminator \
    $_sot_ ∈ _StmtOrTerminator_$ is \
    the single MIR program element observed at one \
    #Location: the statement at `stmtIdx` when that index is \
    in the block's statement list, otherwise the block's \
    terminator (when `stmtIdx` equals `statements.length`, \
    which a #validLocation allows).")
where
  | stmt (s : Statement)
    "A MIR statement."
  | terminator (t : Terminator)
    "A MIR terminator."
  deriving Repr, BEq, Hashable

-- Source-only `Inhabited Statement` so the `[i]!` indexing
-- inside `getStmtOrTerminator` elaborates against the source
-- `defEnum`, which only derives `Repr` / `BEq` / `Hashable`.
-- The Lean exporter adds `Inhabited` automatically to the
-- generated declaration, so this is not re-emitted there.
private instance : Inhabited Statement :=
  ⟨.storageLive ⟨0⟩⟩

defFn getStmtOrTerminator (.plain "getStmtOrTerminator")
  (doc! "Look up the program element at a valid location in a body. When `loc.stmtIdx` is strictly \
    less than the number of statements in the block, returns that statement; when it equals \
    `statements.length` (the terminator slot allowed by #validLocation), returns the block's \
    terminator.")
  (body "The function body." : Body)
  (loc "The location to look up." : Location)
  requires validLocation body loc
  : StmtOrTerminator :=
    let block := body↦blocks ! loc↦block↦index ;
    if loc↦stmtIdx < block↦statements·length
    then
      let stmt := block↦statements ! loc↦stmtIdx ;
      StmtOrTerminator.stmt stmt
    else StmtOrTerminator.terminator block↦terminator
