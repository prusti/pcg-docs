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

-- Bridge from #getStmtOrTerminator's `.stmt s` result to a
-- #validStatement obligation on `s`. Used by callers of
-- `getStmtOrTerminator` (e.g. `Machine.step`) to discharge the
-- #validStatement precondition that #Machine.evalStatement
-- requires for each statement it evaluates. The proof unfolds
-- `getStmtOrTerminator`, splits the if/then/else, and projects
-- the per-statement validity conjunct out of the
-- #validBody-witnessed `blocks.forAll` invariant.
defRaw after =>
open Body in
theorem validStatement_of_getStmtOrTerminator_eq
    (body : Body) (loc : Location)
    (h_validBody : validBody body)
    (h_validLocation : validLocation body loc)
    {s : Statement}
    (h_eq :
      getStmtOrTerminator body loc h_validLocation = .stmt s) :
    validStatement body s := by
  have hblock_lt : loc.block.index < body.blocks.length :=
    h_validLocation.1
  have hblock_in :
      body.blocks[loc.block.index]! ∈ body.blocks := by
    rw [getElem!_pos body.blocks loc.block.index hblock_lt]
    exact List.getElem_mem hblock_lt
  simp only [getStmtOrTerminator] at h_eq
  split at h_eq
  · rename_i hlt
    have hstmt_eq :
        body.blocks[loc.block.index]!.statements[loc.stmtIdx]! =
          s := by injection h_eq
    have hstmt_in :
        s ∈ body.blocks[loc.block.index]!.statements := by
      rw [← hstmt_eq,
        getElem!_pos
          body.blocks[loc.block.index]!.statements
          loc.stmtIdx hlt]
      exact List.getElem_mem hlt
    exact (h_validBody.2.2.1 _ hblock_in).1 _ hstmt_in
  · cases h_eq
