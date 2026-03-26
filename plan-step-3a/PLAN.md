# Step 3a: Init Remaining V Lemma Parity

Status: good; Refinement Needed: no

## Goal

Fill the remaining gaps in V lemma parity for Init types. A comprehensive audit found ~200
additional proof-taking lemmas (beyond those covered by Steps 1-2) that lack V variant
counterparts. Steps 1-2 focused on core value-describing lemmas (push, set, append, map, etc.)
but missed:
- Utility lemmas (sizeOf, attach, pmap, erase, insertIdx, shrink, etc.)
- Entire file areas (BitVec, ByteArray, String, Polymorphic Range)
- Additional lemmas in already-covered files (e.g., Array's swapIfInBounds specialized variants)

## Annotation removal

This step only CREATES V variant lemmas with matching annotations. The corresponding
removal of `@[simp]`/`@[grind]` from the proof-taking counterparts is deferred to
**Step 3c** (`plan-step-3c/PLAN.md`), which must execute after this step completes.

## Signature conventions

See `SIGNATURE_SPEC.md` for full details. Key decisions for this step:
- **`haveI` over `{_ : Nonempty α}`** when an element witness is available in the signature
- **`{_ : Nonempty (α × β)}`** for product types (not separate instances)
- **Drop output-side bounds** when both sides return the same `Classical.ofNonempty` OOB (e.g., `eraseIdx`)
- **Keep bounds** when RHS has a specific value that differs from `Classical.ofNonempty` OOB (e.g., `insertIdx`, `push`, `zip`)

## Methodology

For each sub-step, the elaborating agent must:
1. Read the raw audit list (provided in each stub)
2. **Verify** each entry: grep for the expected V variant name — if it already exists, remove from list
3. **Cross-reference** with Steps 1-2: if a lemma is already planned there, remove from list
4. **Filter out** deprecated lemmas and internal helper lemmas (aux, loop, go suffixes)
5. For each remaining lemma, determine the annotation and write the suggested signature
6. Follow the table format from Steps 1-2 (V lemma | Counterpart | Annotation | Action | Signature)

## Sub-steps

### 3a.1 `src/Init/GetElem.lean` (~4 lemmas)

**Detailed sub-plan**: [step-01/PLAN.md](step-01/PLAN.md)

Lemmas: `getElem_congr`, `getElem_congr_coll`, `getElem_congr_idx`, `of_getElem_eq`.
Note: `getElemV_cons_zero`, `getElemV_cons_succ` already exist — confirmed false positives.

### 3a.2 Array (~30 lemmas across multiple files)

**Detailed sub-plan**: [step-02/PLAN.md](step-02/PLAN.md)

Files: Attach.lean (3), Count.lean (2), Erase.lean (5), Extract.lean (2), Find.lean (3),
InsertIdx.lean (4), Lemmas.lean (~15 remaining), Mem.lean (1: sizeOf_getElemV), OfFn.lean (1),
Zip.lean (1).

Excludes: extract_loop_* internal helpers, deprecated getElem_swap.

### 3a.3 List (~35 lemmas across multiple files)

**Detailed sub-plan**: [step-03/PLAN.md](step-03/PLAN.md)

Files: Attach.lean (3), Count.lean (2), Find.lean (1), MapIdx.lean (1), Nat/Pairwise.lean (3),
Nat/Sublist.lean (1), Nat/TakeDrop.lean (6), Nat/Erase.lean (3), Nat/InsertIdx.lean (4),
TakeDrop.lean (2), Sublist.lean (1), Lemmas.lean (~7 remaining), OfFn.lean (1), Range.lean (1).

### 3a.4 Vector (~35 lemmas across multiple files)

**Detailed sub-plan**: [step-04/PLAN.md](step-04/PLAN.md)

Files: Algebra.lean (6), Attach.lean (3), Count.lean (2), Erase.lean (4), Extract.lean (2),
Find.lean (2), InsertIdx.lean (4), Lemmas.lean (~8 remaining), OfFn.lean (1), Zip.lean (1).

### 3a.5 BitVec (~35 lemmas)

**Detailed sub-plan**: [step-05/PLAN.md](step-05/PLAN.md)

Files: Lemmas.lean (~25), Bitblast.lean (~8: add, sub, mul, udiv, umod, sdiv, srem, smod),
Bootstrap.lean (2).

Note: BitVec `getElem` indexes individual bits. The V variant pattern applies the same way —
`getElemV` with `[Nonempty Bool]` (which is always available). Many have `@[simp, grind =]`.

### 3a.6 ByteArray + String (~10 lemmas)

**Detailed sub-plan**: [step-06/PLAN.md](step-06/PLAN.md)

ByteArray/Lemmas.lean (~3, excluding internal extract_aux), String/Decode.lean (6),
String/Basic.lean (2), String/ForwardSearcher.lean (1), Pattern/String.lean (1).

### 3a.7 Polymorphic Range (~30 lemmas)

**Detailed sub-plan**: [step-07/PLAN.md](step-07/PLAN.md)

Files: Polymorphic/Lemmas.lean (~20: getElem_toList_eq and getElem_toArray_eq across ~10
range types), Polymorphic/IntLemmas.lean (8), Polymorphic/NatLemmas.lean (12).

Note: these are highly repetitive — same pattern (getElem_toList_rco/rcc/roo/roc/rio/ric)
repeated for each range type. A single template approach works for all.

## Summary

| Sub-step | Area | Lemmas to create |
|----------|------|-----------------|
| 3a.1 | GetElem.lean | 1 |
| 3a.2 | Array | 20 |
| 3a.3 | List | 12 |
| 3a.4 | Vector | 23 |
| 3a.5 | BitVec | 31 + `GetElemV` instance prerequisite |
| 3a.6 | ByteArray + String | 0 (no `GetElemV` instances) |
| 3a.7 | Polymorphic Range | 38 |
| **Total** | | **125** |
