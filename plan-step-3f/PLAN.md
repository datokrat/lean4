# Step 3f: Annotation Cleanup for Step 3e V Variants

Status: not started; Refinement Needed: no

## Goal

Remove `@[simp]`/`@[grind]` from proof-taking variant lemmas whose V counterparts
are created in Step 3e with matching annotations.

## Consistency condition

Same as Step 3c: For every annotation removed from a proof-taking lemma, the
corresponding V variant MUST have the matching annotation. Step 3e must create/annotate
the V variant FIRST.

## Bridge lemmas — DO NOT REMOVE

Bridge lemmas (`foo_eq_fooV`) MUST keep `@[simp, grind norm]`. They are rewrite rules.

## Scope

Only lemmas whose proof-taking forms have annotations AND whose V counterparts
are created in Step 3e. Unannotated lemmas produce no entry here.

## Proof-taking annotations to remove

### `src/Init/GetElem.lean` (6 removals) — from Step 3e.0

| Proof-taking lemma | Remove | V counterpart |
|---------------------|--------|-------------------------------|
| `getElem_congr` (line 143) | `@[simp, grind]` | `getElemV_congr` @[simp, grind] |
| `get_getElem?` (line 245) | `@[simp, grind =]` | `get_getElem?_getElemV` @[simp, grind =] |
| `some_getElem_eq_getElem?_iff` (line 299) | `@[simp]` | `some_getElemV_eq_getElem?_iff` @[simp] |
| `getElem?_eq_some_getElem_iff` (line 304) | `@[simp]` | `getElem?_eq_some_getElemV_iff` @[simp] |
| `getElem?_eq_getElem` (line 401) | `@[local simp]` | `getElem?_eq_getElemV` @[local simp] |
| `getInternal_eq_getElem` (line 504) | `@[simp]` | `getInternal_eq_getElemV` @[simp] |

### `src/Init/Data/Array/Lemmas.lean` (3 removals) — from Step 3e.1

| Proof-taking lemma | Remove | V counterpart |
|---------------------|--------|-------------------------------|
| `any_eq` (line 785) | `@[grind =]` | `anyV_eq` @[grind =] |
| `getElem_swapIfInBounds_of_size_le_left` (line 4293) | `@[simp]` | `getElemV_swapIfInBounds_of_size_le_left` @[simp] |
| `getElem_swapIfInBounds_of_size_le_right` (line 4302) | `@[simp]` | `getElemV_swapIfInBounds_of_size_le_right` @[simp] |

### `src/Init/Data/Array/Find.lean` (1 removal) — from Step 3e.1

| Proof-taking lemma | Remove | V counterpart |
|---------------------|--------|-------------------------------|
| `getElem_zero_flatten` (line 139) | `@[grind =]` | `getElemV_zero_flatten` @[grind =] |

### `src/Init/Data/Array/MapIdx.lean` (1 removal) — from Step 3e.1

| Proof-taking lemma | Remove | V counterpart |
|---------------------|--------|-------------------------------|
| `getElem_zipIdx` (line 130) | `@[simp, grind =]` | `getElemV_zipIdx` @[simp, grind =] |

### `src/Init/Data/List/OfFn.lean` (1 removal) — from Step 3e.2

| Proof-taking lemma | Remove | V counterpart |
|---------------------|--------|-------------------------------|
| `ofFn_getElem` (line 115) | `@[simp]` | `ofFn_getElemV` @[simp] |

### `src/Init/Data/List/Nat/Modify.lean` (1 removal) — from Step 3e.2

| Proof-taking lemma | Remove | V counterpart |
|---------------------|--------|-------------------------------|
| `getElem_modifyHead` (line 43) | `@[grind =]` | `getElemV_modifyHead` @[grind =] |

### `src/Init/Data/List/Nat/TakeDrop.lean` (1 removal) — from Step 3e.2

| Proof-taking lemma | Remove | V counterpart |
|---------------------|--------|-------------------------------|
| `getElem_zipWith` (line 600) | `@[simp, grind =]` | `getElemV_zipWith` @[simp, grind =] |

### `src/Init/Data/List/Range.lean` (1 removal) — from Step 3e.2

| Proof-taking lemma | Remove | V counterpart |
|---------------------|--------|-------------------------------|
| `getElem_zipIdx` (line 233) | `@[simp, grind =]` | `getElemV_zipIdx` @[simp, grind =] |

### `src/Init/Data/List/Erase.lean` (2 removals) — from Step 3e.2

| Proof-taking lemma | Remove | V counterpart |
|---------------------|--------|-------------------------------|
| `head_eraseP_mem` (line 306) | `@[grind ←]` | `headV_eraseP_mem` @[grind ←] |
| `getLast_eraseP_mem` (line 310) | `@[grind ←]` | `getLastV_eraseP_mem` @[grind ←] |

### `src/Init/Data/List/Find.lean` (2 removals) — from Step 3e.2

| Proof-taking lemma | Remove | V counterpart |
|---------------------|--------|-------------------------------|
| `head_flatten` (line 153) | `@[grind =]` | `headV_flatten` @[grind =] |
| `getLast_flatten` (line 158) | `@[grind =]` | `getLastV_flatten` @[grind =] |

### `src/Init/Data/List/Attach.lean` (1 removal) — from Step 3e.2

| Proof-taking lemma | Remove | V counterpart |
|---------------------|--------|-------------------------------|
| `getLast_attach` (line 620) | `@[simp, grind =]` | `getLastV_attach` @[simp, grind =] |

### `src/Init/Data/List/Zip.lean` (1 removal) — from Step 3e.2

| Proof-taking lemma | Remove | V counterpart |
|---------------------|--------|-------------------------------|
| `head_zipWith` (line 100) | `@[grind =]` | `headV_zipWith` @[grind =] |

### `src/Init/Data/Vector/Algebra.lean` (1 removal) — from Step 3e.3

| Proof-taking lemma | Remove | V counterpart |
|---------------------|--------|-------------------------------|
| `getElem_neg` (line 60) | `@[simp, grind =]` | `getElemV_neg` @[simp, grind =] |

### `src/Init/Data/Vector/Lemmas.lean` (2 removals) — from Step 3e.3

| Proof-taking lemma | Remove | V counterpart |
|---------------------|--------|-------------------------------|
| `getElem_append_left` (line 1816) | `@[simp]` | `getElemV_append_left` @[simp] |
| `getElem_append_right` (line 1820) | `@[simp]` | `getElemV_append_right` @[simp] |

### `src/Init/Data/Vector/Extract.lean` (1 removal) — from Step 3e.3

| Proof-taking lemma | Remove | V counterpart |
|---------------------|--------|-------------------------------|
| `getElem?_extract_of_lt` (line 91) | `@[simp]` | `getElemV?_extract_of_lt` @[simp] |

### `src/Init/Data/BitVec/Lemmas.lean` (14 removals) — from Step 3e.4

| Proof-taking lemma | Remove | V counterpart |
|---------------------|--------|-------------------------------|
| `getElem_zero` | `@[simp, grind =]` | `getElemV_zero` @[simp, grind =] |
| `getElem_one` | `@[simp, grind =]` | `getElemV_one` @[simp, grind =] |
| `getElem_ofFin` | `@[simp]` | `getElemV_ofFin` @[simp] |
| `getElem_cast` | `@[simp, grind =]` | `getElemV_cast` @[simp, grind =] |
| `getElem_allOnes` | `@[simp, grind =]` | `getElemV_allOnes` @[simp, grind =] |
| `getElem_or` | `@[simp, grind =]` | `getElemV_or` @[simp, grind =] |
| `getElem_and` | `@[simp, grind =]` | `getElemV_and` @[simp, grind =] |
| `getElem_xor` | `@[simp, grind =]` | `getElemV_xor` @[simp, grind =] |
| `getElem_not` | `@[simp, grind =]` | `getElemV_not` @[simp, grind =] |
| `getElem_ushiftRight` | `@[simp, grind =]` | `getElemV_ushiftRight` @[simp, grind =] |
| `getElem_extractLsb'` | `@[simp, grind =]` | `getElemV_extractLsb'` @[simp, grind =] |
| `getElem_extract` | `@[simp, grind =]` | `getElemV_extract` @[simp, grind =] |
| `getElem_shiftLeftZeroExtend` | `@[simp]` | `getElemV_shiftLeftZeroExtend` @[simp] |
| `getElem_ofBoolListBE` | `@[simp, grind =]` | `getElemV_ofBoolListBE` @[simp, grind =] |

### `src/Init/Data/BitVec/Bootstrap.lean` (1 removal) — from Step 3e.4

| Proof-taking lemma | Remove | V counterpart |
|---------------------|--------|-------------------------------|
| `getElem_cons` | none currently; V variant adds `@[grind =]` | `getElemV_cons` @[grind =] — NEW annotation, no removal needed |

Note: `getElem_cons` has no annotation in the source. The V variant `getElemV_cons` adds
`@[grind =]` as a new annotation. No removal from the counterpart.

### `src/Init/Data/BitVec/Lemmas.lean` (2 additional removals) — from Step 3e.4

| Proof-taking lemma | Remove | V counterpart |
|---------------------|--------|-------------------------------|
| `getElem_concat_zero` | `@[simp]` | `getElemV_concat_zero` @[simp] |
| `getElem_concat_succ` | `@[simp]` | `getElemV_concat_succ` @[simp] |

### `src/Init/Data/BitVec/Lemmas.lean` — `getElem_rev` and `getElem_reverse` (2 removals) — from Step 3e.4

| Proof-taking lemma | Remove | V counterpart |
|---------------------|--------|-------------------------------|
| `getElem_rev` | `@[grind =]` | `getElemV_rev` @[grind =] |
| `getElem_reverse` | `@[grind =]` | `getElemV_reverse` @[grind =] |

### `src/Init/Data/ByteArray/Lemmas.lean` (1 removal) — from Step 3e.5

| Proof-taking lemma | Remove | V counterpart |
|---------------------|--------|-------------------------------|
| `getElem_append_left` (line 111) | `@[simp]` | `getElemV_append_left` @[simp] |

### Std files — no annotation removals needed (from Step 3e.6)

All V variants created in Step 3e.6 (Parts A, B, C) have counterparts that are
unannotated. No annotation removals are needed for Std files.

## Totals

| Category | Count |
|----------|-------|
| Files affected | 17 |
| Annotation removals (Init) | 42 |
| Annotation removals (Std) | 0 |
| **Total annotation removals** | **42** |

### Breakdown by source step

| Step | Area | Count |
|------|------|-------|
| 3e.0 | GetElem.lean | 6 |
| 3e.1 | Array (Lemmas, Find, MapIdx) | 5 |
| 3e.2 | List (OfFn, Nat/Modify, Nat/TakeDrop, Range, Erase, Find, Attach, Zip) | 10 |
| 3e.3 | Vector (Algebra, Lemmas, Extract) | 4 |
| 3e.4 | BitVec (Lemmas) | 18 |
| 3e.5 | ByteArray (Lemmas) | 1 |
| 3e.6 | Std | 0 |

### Consolidated by file

| File | Removals |
|------|----------|
| `src/Init/GetElem.lean` | 6 |
| `src/Init/Data/Array/Lemmas.lean` | 3 |
| `src/Init/Data/Array/Find.lean` | 1 |
| `src/Init/Data/Array/MapIdx.lean` | 1 |
| `src/Init/Data/List/OfFn.lean` | 1 |
| `src/Init/Data/List/Nat/Modify.lean` | 1 |
| `src/Init/Data/List/Nat/TakeDrop.lean` | 1 |
| `src/Init/Data/List/Range.lean` | 1 |
| `src/Init/Data/List/Erase.lean` | 2 |
| `src/Init/Data/List/Find.lean` | 2 |
| `src/Init/Data/List/Attach.lean` | 1 |
| `src/Init/Data/List/Zip.lean` | 1 |
| `src/Init/Data/Vector/Algebra.lean` | 1 |
| `src/Init/Data/Vector/Lemmas.lean` | 2 |
| `src/Init/Data/Vector/Extract.lean` | 1 |
| `src/Init/Data/BitVec/Lemmas.lean` | 18 |
| `src/Init/Data/ByteArray/Lemmas.lean` | 1 |

## Dependencies

This step MUST be executed AFTER Step 3e completes (V variants must exist
before their proof-taking counterparts' annotations are removed).
