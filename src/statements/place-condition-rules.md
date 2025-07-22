# Rules for Determining Place Conditions

Place conditions are computed in terms of *triples*, where a triple is a pair (*pre*, *post*) where *pre* is a place condition and *post* is either a place condition or `None`.

The place conditions for each phase are determined by two sets of triples: the
*operand triples* and the *main triples*. The place conditions for the
`PreOperands` phase is the set of conditions in the *pre*s of the operand
triples. The `PostOperands` phase is the set of conditions in the *post*s of the
operand triples. `PreMain` and `PostMain` are defined accordingly.

## Determining Operand Triples for a Statement

1. For each operand $o$ in the statement:
    1. If $o$ takes the form `copy p`:
        - Add `(p: R, None)` to the operand triples
    1. If $o$ takes the form `move p`:
        - Add `(p: E, p: W)` to the operand triples
2. For each rvalue $r$ in the statement:
    1. If $r$ takes the form `&p`:
        - Add `(p: R, p: R)` to the operand triples
    2. If $r$ takes the form `&mut p`:
        - If the borrow is a two-phase borrow:
            - Add `(ExpandTwoPhase p, p: R)` to the operand triples
        - Otherwise, add `(p: E, RemoveCapability p)` to the operand triples
    3. If $r$ takes the form `*mut p`:
        - Add `(p: E, None)` to the operand triples
    4. If $r$ takes the form `*const p`:
        - Add `(p: R, None)` to the operand triples
    5. If $r$ takes the form `len(p)`, `discriminant(p)` or `CopyForDeref(p)`:
        - Add `(p: R, None)` to the operand triples

## Determining Main Triples for a Statement

The rule depends on the statement type:

1. `Assign(p, r)`
    1. If `r` takes the form `&fake q`:
        - Add `(p: W, None)` to the main triples
    2. If `r` takes the form `ShallowInitBox o t`
        - Add `(p: W, p: e)` to the main triples
    3. Otherwise, add `(p: W, p: E)` to the main triples
2. `FakeRead(_, p)`
    1. Add `(p: R, None)` to the main triples
3. `SetDiscriminant(p, ..)`
    1. Add `(p: E, None)` to the main triples
3. `Deinit(p)`
    1. Add `(p: E, p: w)` to the main triples
4. `StorageLive(v)`
    1. Add `(Unalloc v, AllocateOrDeallocate v)` to the main triples
5. `StorageDead(v)`
    1. Add `(AllocateOrDeallocate v, Unalloc v)` to the main triples
6. `Retag(_, p)`
    1. Add `(p: E, None)` to the main triples

## Determining Main Triples for a Terminator

The rule depends on the terminator type:

1. `Return`
    1. Add `(Return, _0: w)` to the main triples
2. `Drop(p)`
    1. Add `(p: W, None)` to the main triples
3. `Call(p, _)`
    1. Add `(p: W, p: E)` to the main triples
4. `Yield(p, _)`
    1. Add `(p: W, p: E)` to the main triples


