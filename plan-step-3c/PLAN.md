# Step 3c: Annotation Cleanup for Steps 3a/3b V Variants

Status: not started; Refinement Needed: no

## Goal

Remove `@[simp]`/`@[grind]` from proof-taking variant lemmas whose V counterparts
are created in Steps 3a and 3b with matching annotations.

## Consistency condition

For every annotation removed from a proof-taking lemma, the corresponding V variant
MUST have the matching annotation. Steps 3a/3b must create/annotate the V variant
FIRST, before this step removes the annotation from the proof-taking lemma. This is
a hard coupling — annotation removal and V-lemma addition are atomic.

## Bridge lemmas — DO NOT REMOVE

Bridge lemmas (`foo_eq_fooV`) MUST keep `@[simp, grind norm]`. They are rewrite rules.

## Scope

Only lemmas whose proof-taking forms STILL have annotations (verified by grep against
current source) are listed. V variants that are unannotated, or whose proof-taking
counterpart is already unannotated, produce no entry here.

## Proof-taking annotations still to remove

### `src/Init/GetElem.lean` (1 removal)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.1) |
|---------------------|--------|-------------------------------|
| `getElem_cons_drop` | `@[simp]` | `getElemV_cons_drop` @[simp] |

### `src/Init/Data/Array/Attach.lean` (3 removals)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.2) |
|---------------------|--------|-------------------------------|
| `getElem_pmap` | `@[simp, grind =]` | `getElemV_pmap` @[simp, grind =] |
| `getElem_attachWith` | `@[simp, grind =]` | `getElemV_attachWith` @[simp, grind =] |
| `getElem_attach` | `@[simp, grind =]` | `getElemV_attach` @[simp, grind =] |

### `src/Init/Data/Array/Erase.lean` (1 removal)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.2) |
|---------------------|--------|-------------------------------|
| `getElem_eraseIdx` | `@[grind =]` | `getElemV_eraseIdx` @[grind =] |

### `src/Init/Data/Array/InsertIdx.lean` (1 removal)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.2) |
|---------------------|--------|-------------------------------|
| `getElem_insertIdx` | `@[grind =]` | `getElemV_insertIdx` @[grind =] |

### `src/Init/Data/Array/Lemmas.lean` (4 removals)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.2) |
|---------------------|--------|-------------------------------|
| `getElem_swapIfInBounds_left` | `@[simp]` | `getElemV_swapIfInBounds_left` @[simp] |
| `getElem_swapIfInBounds_right` | `@[simp]` | `getElemV_swapIfInBounds_right` @[simp] |
| `getElem_swapIfInBounds_of_ne_of_ne` | `@[simp]` | `getElemV_swapIfInBounds_of_ne_of_ne` @[simp] |
| `getElem_range` | `@[simp, grind =]` | `getElemV_range` @[simp, grind =] |

### `src/Init/Data/Array/Mem.lean` (1 removal)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.2) |
|---------------------|--------|-------------------------------|
| `sizeOf_getElem` | `@[simp]` | `sizeOf_getElemV` @[simp] |

### `src/Init/Data/Array/Zip.lean` (1 removal)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.2) |
|---------------------|--------|-------------------------------|
| `getElem_zip` | `@[simp, grind =]` | `getElemV_zip` @[simp, grind =] |

### `src/Init/Data/List/Attach.lean` (3 removals)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.3) |
|---------------------|--------|-------------------------------|
| `getElem_pmap` | `@[simp, grind =]` | `getElemV_pmap` @[simp, grind =] |
| `getElem_attachWith` | `@[simp, grind =]` | `getElemV_attachWith` @[simp, grind =] |
| `getElem_attach` | `@[simp, grind =]` | `getElemV_attach` @[simp, grind =] |

### `src/Init/Data/List/Nat/Erase.lean` (1 removal)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.3) |
|---------------------|--------|-------------------------------|
| `getElem_eraseIdx` | `@[grind =]` | `getElemV_eraseIdx` @[grind =] |

### `src/Init/Data/List/Nat/InsertIdx.lean` (1 removal)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.3) |
|---------------------|--------|-------------------------------|
| `getElem_insertIdx` | `@[grind =]` | `getElemV_insertIdx` @[grind =] |

### `src/Init/Data/List/Nat/Basic.lean` (1 removal)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.3) |
|---------------------|--------|-------------------------------|
| `getElem_intersperse` | `@[grind =]` | `getElemV_intersperse` @[grind =] |

### `src/Init/Data/Vector/Algebra.lean` (6 removals)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.4) |
|---------------------|--------|-------------------------------|
| `getElem_zero` | `@[simp, grind =]` | `getElemV_zero` @[simp, grind =] |
| `getElem_add` | `@[simp, grind =]` | `getElemV_add` @[simp, grind =] |
| `getElem_sub` | `@[simp, grind =]` | `getElemV_sub` @[simp, grind =] |
| `getElem_mul` | `@[simp, grind =]` | `getElemV_mul` @[simp, grind =] |
| `getElem_hmul` | `@[simp, grind =]` | `getElemV_hmul` @[simp, grind =] |
| `getElem_smul` | `@[simp, grind =]` | `getElemV_smul` @[simp, grind =] |

### `src/Init/Data/Vector/Attach.lean` (3 removals)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.4) |
|---------------------|--------|-------------------------------|
| `getElem_pmap` | `@[simp, grind =]` | `getElemV_pmap` @[simp, grind =] |
| `getElem_attachWith` | `@[simp, grind =]` | `getElemV_attachWith` @[simp, grind =] |
| `getElem_attach` | `@[simp, grind =]` | `getElemV_attach` @[simp, grind =] |

### `src/Init/Data/Vector/Erase.lean` (1 removal)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.4) |
|---------------------|--------|-------------------------------|
| `getElem_eraseIdx` | `@[grind =]` | `getElemV_eraseIdx` @[grind =] |

### `src/Init/Data/Vector/Extract.lean` (1 removal)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.4) |
|---------------------|--------|-------------------------------|
| `push_extract_getElem` | `@[simp]` | `push_extract_getElemV` @[simp] |

### `src/Init/Data/Vector/Find.lean` (1 removal)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.4) |
|---------------------|--------|-------------------------------|
| `getElem_zero_flatten` | `@[grind =]` | `getElemV_zero_flatten` @[grind =] |

### `src/Init/Data/Vector/InsertIdx.lean` (1 removal)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.4) |
|---------------------|--------|-------------------------------|
| `getElem_insertIdx` | `@[grind =]` | `getElemV_insertIdx` @[grind =] |

### `src/Init/Data/Vector/Lemmas.lean` (1 removal)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.4) |
|---------------------|--------|-------------------------------|
| `getElem_push` | `@[grind =]` | `getElemV_push` @[grind =] |

### `src/Init/Data/Vector/OfFn.lean` (1 removal)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.4) |
|---------------------|--------|-------------------------------|
| `ofFn_getElem` | `@[simp]` | `ofFn_getElemV` @[simp] |

### `src/Init/Data/Vector/Zip.lean` (1 removal)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.4) |
|---------------------|--------|-------------------------------|
| `getElem_zip` | `@[simp, grind =]` | `getElemV_zip` @[simp, grind =] |

### `src/Init/Data/BitVec/Basic.lean` (2 removals)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.5) |
|---------------------|--------|-------------------------------|
| `getElem_eq_testBit_toNat` | `@[grind =_]` | `getElemV_eq_testBit_toNat` @[grind =_] |
| `getLsbD_eq_getElem` | `@[simp, grind =]` | `getLsbD_eq_getElemV` @[simp, grind =] |

### `src/Init/Data/BitVec/Bootstrap.lean` (2 removals)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.5) |
|---------------------|--------|-------------------------------|
| `getElem_setWidth'` | `@[grind =]` | `getElemV_setWidth'` @[grind =] |
| `getElem_setWidth` | `@[simp, grind =]` | `getElemV_setWidth` @[simp, grind =] |

### `src/Init/Data/BitVec/Lemmas.lean` (16 removals)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.5) |
|---------------------|--------|-------------------------------|
| `getElem_ofBool_zero` | `@[simp, grind =]` | `getElemV_ofBool_zero` @[simp, grind =] |
| `getElem_ofBool` | `@[simp]` | `getElemV_ofBool` @[simp] |
| `getElem_shiftLeft` | `@[simp, grind =]` | `getElemV_shiftLeft` @[simp, grind =] |
| `getElem_sshiftRight` | `@[grind =]` | `getElemV_sshiftRight` @[grind =] |
| `getElem_signExtend` | `@[grind =]` | `getElemV_signExtend` @[grind =] |
| `getElem_append` | `@[grind =]` | `getElemV_append` @[grind =] |
| `getElem_concat` | `@[grind =]` | `getElemV_concat` @[grind =] |
| `getElem_shiftConcat` | `@[grind =]` | `getElemV_shiftConcat` @[grind =] |
| `getElem_shiftConcat_zero` | `@[simp]` | `getElemV_shiftConcat_zero` @[simp] |
| `getElem_shiftConcat_succ` | `@[simp]` | `getElemV_shiftConcat_succ` @[simp] |
| `getElem_fill` | `@[simp, grind =]` | `getElemV_fill` @[simp, grind =] |
| `getElem_rotateLeft` | `@[simp, grind =]` | `getElemV_rotateLeft` @[simp, grind =] |
| `getElem_rotateRight` | `@[simp, grind =]` | `getElemV_rotateRight` @[simp, grind =] |
| `getElem_twoPow` | `@[simp, grind =]` | `getElemV_twoPow` @[simp, grind =] |
| `getElem_replicate` | `@[simp, grind =]` | `getElemV_replicate` @[simp, grind =] |
| `getElem_abs` | `@[grind =]` | `getElemV_abs` @[grind =] |

### `src/Init/Data/Range/Polymorphic/IntLemmas.lean` (8 removals)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.7) |
|---------------------|--------|-------------------------------|
| `getElem_toList_rco` | `@[simp]` | `getElemV_toList_rco` @[simp] |
| `getElem_toArray_rco` | `@[simp]` | `getElemV_toArray_rco` @[simp] |
| `getElem_toList_rcc` | `@[simp]` | `getElemV_toList_rcc` @[simp] |
| `getElem_toArray_rcc` | `@[simp]` | `getElemV_toArray_rcc` @[simp] |
| `getElem_toList_roo` | `@[simp]` | `getElemV_toList_roo` @[simp] |
| `getElem_toArray_roo` | `@[simp]` | `getElemV_toArray_roo` @[simp] |
| `getElem_toList_roc` | `@[simp]` | `getElemV_toList_roc` @[simp] |
| `getElem_toArray_roc` | `@[simp]` | `getElemV_toArray_roc` @[simp] |

### `src/Init/Data/Range/Polymorphic/NatLemmas.lean` (12 removals)

| Proof-taking lemma | Remove | V counterpart (from Step 3a.7) |
|---------------------|--------|-------------------------------|
| `getElem_toList_rco` | `@[simp]` | `getElemV_toList_rco` @[simp] |
| `getElem_toArray_rco` | `@[simp]` | `getElemV_toArray_rco` @[simp] |
| `getElem_toList_rcc` | `@[simp]` | `getElemV_toList_rcc` @[simp] |
| `getElem_toArray_rcc` | `@[simp]` | `getElemV_toArray_rcc` @[simp] |
| `getElem_toList_roo` | `@[simp]` | `getElemV_toList_roo` @[simp] |
| `getElem_toArray_roo` | `@[simp]` | `getElemV_toArray_roo` @[simp] |
| `getElem_toList_roc` | `@[simp]` | `getElemV_toList_roc` @[simp] |
| `getElem_toArray_roc` | `@[simp]` | `getElemV_toArray_roc` @[simp] |
| `getElem_toList_rio` | `@[simp]` | `getElemV_toList_rio` @[simp] |
| `getElem_toArray_rio` | `@[simp]` | `getElemV_toArray_rio` @[simp] |
| `getElem_toList_ric` | `@[simp]` | `getElemV_toList_ric` @[simp] |
| `getElem_toArray_ric` | `@[simp]` | `getElemV_toArray_ric` @[simp] |

### Std files — no annotation removals needed

Steps 3b.1–3b.4 create only 6 V variant lemmas total. None of the corresponding
proof-taking lemmas have annotations to remove:
- `getElem_insertIfNew` (TreeMap/Lemmas.lean): no annotation
- `getElem_union_of_mem_right` (both TreeMap files): no annotation
- `minKey_eq_getElem_keysArray` (TreeMap/Lemmas.lean): no annotation
- `minKey_eq_head_keys` (DTreeMap/Lemmas.lean): no annotation
- `minKey_eq_getElem_keysArray` (DTreeMap/Lemmas.lean): no annotation

## Totals

| Category | Count |
|----------|-------|
| Files affected | 25 |
| Annotation removals (Init) | 74 |
| Annotation removals (Std) | 0 |
| **Total annotation removals** | **74** |

### Breakdown by area

| Area | Count |
|------|-------|
| GetElem.lean | 1 |
| Array (Attach, Erase, InsertIdx, Lemmas, Mem, Zip) | 11 |
| List (Attach, Nat/Erase, Nat/InsertIdx, Nat/Basic) | 6 |
| Vector (Algebra, Attach, Erase, Extract, Find, InsertIdx, Lemmas, OfFn, Zip) | 16 |
| BitVec (Basic, Bootstrap, Lemmas) | 20 |
| Range (IntLemmas, NatLemmas) | 20 |

## Dependencies

This step MUST be executed AFTER Steps 3a and 3b complete (V variants must exist
before their proof-taking counterparts' annotations are removed). It can be executed
concurrently with or after Step 3 (which handles annotation removals for Steps 1-2
V variants).
