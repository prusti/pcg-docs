import Core.Dsl.DefFn
import MIR.Place
import PCG.Obtain.Tree
import PCG.Owned.OwnedLocal
import PCG.Owned.OwnedState

-- ══════════════════════════════════════════════
-- Lifting the tree operation to the owned state
-- ══════════════════════════════════════════════

defFn setOwnedLocalAt (.plain "setOwnedLocalAt")
  (.plain "Replace the owned local at a given index in an \
    owned state. Out-of-range indices are left unchanged.")
  (os "The owned state." : OwnedState)
  (idx "The local index to replace." : Nat)
  (newOl "The replacement owned local." : OwnedLocal)
  displayed (#os, .sym .lbracket, #idx, .sym .mapsto, #newOl,
             .sym .rbracket)
  : OwnedState :=
    OwnedState⟨os↦locals·zipIdx·map fun ⟨ol, i⟩ =>
      if i == idx then newOl else ol⟩

defFn obtainWriteOwned (.plain "obtainWriteOwned")
  (doc! "Obtain write ($__W__$) capability on an owned place \
    by restructuring its local's initialisation tree. Returns \
    `None` when the local is unallocated or when the tree \
    restructuring fails (unsupported shape, shallow leaf on \
    the path, etc.).")
  (os "The owned state." : OwnedState)
  (p "The place to obtain." : Place)
  : Option OwnedState :=
    let idx := p↦«local»↦index ;
    let ol ← os↦locals !! idx ;
    match ol with
    | .allocated it =>
        let newIt ← obtainWriteInTree it p↦projection ;
        Some (setOwnedLocalAt os idx (.allocated newIt))
    | .unallocated => None
    end
