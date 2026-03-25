# Step 3: Annotation Cleanup

Status: good; Refinement Needed: no

## Goal
Remove `@[simp]`/`@[grind]` from proof-taking variant lemmas that still have them.

## Consistency condition
For every annotation removed from a proof-taking lemma, the corresponding V variant
MUST have the matching annotation. If the V variant doesn't exist or lacks the annotation,
Steps 1-2 must create/annotate it FIRST.

## Already-removed annotations
Commit 5a80909eff already removed annotations from many proof-taking lemmas in Init and Std
files (Array `back_*`, List `head_*`/`getLast_*`, Option `get_*`, and many Std types).
Those removals are addressed by V lemma creation and annotation in Steps 1-2. They are
NOT re-listed here since the annotations are already gone.

## Bridge lemmas — DO NOT REMOVE
Bridge lemmas (`foo_eq_fooV`) MUST keep `@[simp, grind norm]`. They are rewrite rules.

## Proof-taking annotations still to remove

Unified format: each row is one annotation removal, paired with the V counterpart created in Steps 1-2.

### `src/Init/Data/List/Scan/Lemmas.lean` (5 removals)

| Proof-taking lemma | Remove | V counterpart (from Step 1.7) |
|---------------------|--------|-------------------------------|
| `head_scanl` | `@[simp]` | `headV_scanl` @[simp] |
| `head_scanr` | `@[simp]` | `headV_scanr` @[simp] |
| `getLast_scanr` | `@[grind =]` | `getLastV_scanr` @[grind =] |
| `getElem_scanl` | `@[simp, grind =]` | `getElemV_scanl` @[simp, grind =] |
| `getElem_scanr` | `@[simp, grind =]` | `getElemV_scanr` @[simp, grind =] |

### `src/Init/Data/Array/Lemmas.lean` (20 removals)

| Proof-taking lemma | Remove | V counterpart (from Step 1.1) |
|---------------------|--------|-------------------------------|
| `getElem_push_eq` | `@[simp]` | `getElemV_push_eq` @[simp] |
| `getElem_push` | `@[grind =]` | `getElemV_push` @[grind =] |
| `getElem_set_self` | `@[simp]` | `getElemV_set_self` @[simp] |
| `getElem_set_ne` | `@[simp]` | `getElemV_set_ne` @[simp] |
| `getElem_set` | `@[grind =]` | `getElemV_set` @[grind =] |
| `set_getElem_self` | `@[simp]` | `set_getElemV_self` @[simp] |
| `getElem_setIfInBounds` | `@[grind =]` | `getElemV_setIfInBounds` @[grind =] |
| `getElem_setIfInBounds_self` | `@[simp]` | `getElemV_setIfInBounds_self` @[simp] |
| `getElem_setIfInBounds_ne` | `@[simp]` | `getElemV_setIfInBounds_ne` @[simp] |
| `getElem_filter` | `@[grind ←]` | `getElemV_filter` @[grind ←] |
| `getElem_append` | `@[grind =]` | `getElemV_append` @[grind =] |
| `getElem_append_left` | `@[simp]` | `getElemV_append_left` @[simp] |
| `getElem_append_right` | `@[simp]` | `getElemV_append_right` @[simp] |
| `getElem_modify` | `@[grind =]` | `getElemV_modify` @[grind =] |
| `getElem_swap_right` | `@[simp]` | `getElemV_swap_right` @[simp] |
| `getElem_swap_left` | `@[simp]` | `getElemV_swap_left` @[simp] |
| `getElem_swap_of_ne` | `@[simp]` | `getElemV_swap_of_ne` @[simp] |
| `getElem_swapIfInBounds` | `@[grind =]` | `getElemV_swapIfInBounds` @[grind =] |
| `getElem_replace` | `@[grind =]` | `getElemV_replace` @[grind =] |
| `getElem_ofFn` | `@[simp]` | `getElemV_ofFn` @[simp] |

### `src/Init/Data/Array/MapIdx.lean` (1 removal)

| Proof-taking lemma | Remove | V counterpart (from Step 1.1) |
|---------------------|--------|-------------------------------|
| `back_mapIdx` | `@[simp, grind =]` | `backV_mapIdx` @[simp, grind =] |

### `src/Init/Data/List/Lemmas.lean` (3 removals)

| Proof-taking lemma | Remove | V counterpart (from Step 1.3) |
|---------------------|--------|-------------------------------|
| `getElem_singleton` | `@[simp]` | `getElemV_singleton` @[simp] |
| `getElem_map` | `@[simp, grind =]` | `getElemV_map` @[simp, grind =] |
| `getElem_append` | `@[grind =]` | `getElemV_append` @[grind =] |

### `src/Init/Data/List/Nat/Modify.lean` (5 removals)

| Proof-taking lemma | Remove | V counterpart (from Step 1.4) |
|---------------------|--------|-------------------------------|
| `getElem_modifyHead_zero` | `@[simp]` | `getElemV_modifyHead_zero` @[simp] |
| `getElem_modifyHead_succ` | `@[simp]` | `getElemV_modifyHead_succ` @[simp] |
| `getElem_modify` | `@[grind =]` | `getElemV_modify` @[grind =] |
| `getElem_modify_eq` | `@[simp]` | `getElemV_modify_eq` @[simp] |
| `getElem_modify_ne` | `@[simp]` | `getElemV_modify_ne` @[simp] |

### `src/Init/Data/List/Nat/Basic.lean` (2 removals)

| Proof-taking lemma | Remove | V counterpart (from Step 1.5) |
|---------------------|--------|-------------------------------|
| `getElem_intersperse_two_mul` | `@[simp]` | `getElemV_intersperse_two_mul` @[simp] |
| `getElem_intersperse_two_mul_add_one` | `@[simp]` | `getElemV_intersperse_two_mul_add_one` @[simp] |

### `src/Init/Data/Vector/Lemmas.lean` (24 removals)

All 24 `getElem_*` lemmas listed in Step 1.2, with matching annotations.

## Totals

| Category | Count |
|----------|-------|
| Annotation removals (this step) | 60 |
| V lemma creations (Steps 1-2) | ~120 |
| Annotation additions to existing V lemmas (Steps 1-2) | ~44 |
