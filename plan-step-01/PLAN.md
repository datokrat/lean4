# Step 1: Init V Lemma Parity

Status: good; Refinement Needed: no

## Goal
Achieve full lemma parity between proof-taking operations and V variants in Init types.

All tables use a unified format:
- **V lemma**: the V variant to create or annotate
- **Proof-taking counterpart**: the proof-taking lemma it mirrors
- **Annotation**: the annotation the V lemma must have
- **Action**: `create` (V lemma missing), `annotate` (V lemma exists but lacks annotation)

## 1.1 `src/Init/Data/Array/Lemmas.lean`

### `backV` (12 lemmas: 11 create + 1 in MapIdx)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `backV_singleton` | `back_singleton` | `@[grind =]` | create |
| `backV_eq_getElemV` | `back_eq_getElem` | `@[grind =]` | create |
| `backV_mem` | `back_mem` | `@[simp]` | create |
| `backV_pop` | `back_pop` | none | create |
| `backV_append_of_size_pos` | `back_append_of_size_pos` | `@[simp]` | create |
| `backV_append` | `back_append` | `@[grind =]` | create |
| `backV_append_right` | (no direct counterpart) | none | create |
| `backV_append_left` | (no direct counterpart) | none | create |
| `backV_filter_of_pos` | `back_filter_of_pos` | none | create |
| `backV_filterMap_of_eq_some` | `back_filterMap_of_eq_some` | none | create |
| `backV_replicate` | `back_replicate` | `@[simp]` | create |

### `backV` in `src/Init/Data/Array/MapIdx.lean` (1 lemma)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `backV_mapIdx` | `back_mapIdx` | `@[simp, grind =]` | create |

### `getElemV` (20 lemmas)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getElemV_push_eq` | `getElem_push_eq` (line 183) | `@[simp]` | create |
| `getElemV_push` | `getElem_push` (line 187) | `@[grind =]` | create |
| `getElemV_set_self` | `getElem_set_self` (line 891) | `@[simp]` | create |
| `getElemV_set_ne` | `getElem_set_ne` (line 899) | `@[simp]` | create |
| `getElemV_set` | `getElem_set` (line 908) | `@[grind =]` | create |
| `set_getElemV_self` | `set_getElem_self` (line 918) | `@[simp]` | create |
| `getElemV_setIfInBounds` | `getElem_setIfInBounds` (line 996) | `@[grind =]` | create |
| `getElemV_setIfInBounds_self` | `getElem_setIfInBounds_self` (line 1005) | `@[simp]` | create |
| `getElemV_setIfInBounds_ne` | `getElem_setIfInBounds_ne` (line 1010) | `@[simp]` | create |
| `getElemV_filter` | `getElem_filter` (line 1455) | `@[grind ←]` | create |
| `getElemV_append` | `getElem_append` (line 1819) | `@[grind =]` | create |
| `getElemV_append_left` | `getElem_append_left` (line 1825) | `@[simp]` | create |
| `getElemV_append_right` | `getElem_append_right` (line 1833) | `@[simp]` | create |
| `getElemV_modify` | `getElem_modify` (line 3987) | `@[grind =]` | create |
| `getElemV_swap_right` | `getElem_swap_right` (line 4024) | `@[simp]` | create |
| `getElemV_swap_left` | `getElem_swap_left` (line 4028) | `@[simp]` | create |
| `getElemV_swap_of_ne` | `getElem_swap_of_ne` (line 4032) | `@[simp]` | create |
| `getElemV_swapIfInBounds` | `getElem_swapIfInBounds` (line 4071) | `@[grind =]` | create |
| `getElemV_replace` | `getElem_replace` (line 4174) | `@[grind =]` | create |
| `getElemV_ofFn` | `getElem_ofFn` (line 4282) | `@[simp]` | create |

Note: List has its own `getElemV_append_left`/`right` in BasicAux.lean and `getElemV_ofFn`
in OfFn.lean. Array needs separate versions since `Array.getElem_append_left` etc. are
separate `@[simp]` lemmas.

## 1.2 `src/Init/Data/Vector/Lemmas.lean`

### `backV` (10 lemmas)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `backV_singleton` | `back_singleton` | `@[grind =]` | create |
| `backV_eq_getElemV` | `back_eq_getElem` | `@[grind =]` | create |
| `backV_mem` | `back_mem` | `@[simp]` | create |
| `backV_pop` | `back_pop` | none | create |
| `backV_append_of_neZero` | `back_append_of_neZero` | `@[simp]` | create |
| `backV_append` | `back_append` | `@[grind =]` | create |
| `backV_append_right` | (no direct counterpart) | none | create |
| `backV_append_left` | (no direct counterpart) | none | create |
| `backV_replicate` | `back_replicate` | `@[simp]` | create |
| `push_pop_backV` | `push_pop_back` | `@[simp]` | create |

### `getElemV` (24 lemmas — currently ZERO exist)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getElemV_mk` | `getElem_mk` (line 52) | `@[simp]` | create |
| `getElemV_toList` | `getElem_toList` (line 557) | `@[simp]` | create |
| `getElemV_cast` | `getElem_cast` (line 793) | `@[simp]` | create |
| `getElem?_eq_getElemV` | `getElem?_eq_getElem` (line 862) | `@[simp]` | create |
| `getElemV_push_lt` | `getElem_push_lt` (line 900) | `@[simp]` | create |
| `getElemV_push_eq` | `getElem_push_eq` (line 906) | `@[simp]` | create |
| `getElemV_mem` | `getElem_mem` (line 934) | `@[simp]` | create |
| `getElemV_set` | `getElem_set` (line 1293) | `@[grind =]` | create |
| `getElemV_set_self` | `getElem_set_self` (line 1298) | `@[simp]` | create |
| `getElemV_set_ne` | `getElem_set_ne` (line 1303) | `@[simp]` | create |
| `set_getElemV_self` | `set_getElem_self` (line 1318) | `@[simp]` | create |
| `getElemV_setIfInBounds` | `getElem_setIfInBounds` (line 1354) | `@[grind =]` | create |
| `getElemV_setIfInBounds_self` | `getElem_setIfInBounds_self` (line 1359) | `@[simp]` | create |
| `getElemV_setIfInBounds_ne` | `getElem_setIfInBounds_ne` (line 1364) | `@[simp]` | create |
| `getElemV_flatten` | `getElem_flatten` (line 1916) | `@[simp]` | create |
| `getElemV_flatMap` | `getElem_flatMap` (line 2049) | `@[simp]` | create |
| `getElemV_extract` | `getElem_extract` (line 2316) | `@[simp]` | create |
| `getElemV_pop'` | `getElem_pop'` (line 2725) | `@[simp]` | create |
| `getElemV_replace` | `getElem_replace` (line 2930) | `@[grind =]` | create |
| `getElemV_swap` | `getElem_swap` (line 3021) | `@[grind =]` | create |
| `getElemV_swap_right` | `getElem_swap_right` (line 3026) | `@[simp]` | create |
| `getElemV_swap_left` | `getElem_swap_left` (line 3030) | `@[simp]` | create |
| `getElemV_swap_of_ne` | `getElem_swap_of_ne` (line 3034) | `@[simp]` | create |
| `getElemV_drop` | `getElem_drop` (line 3065) | `@[grind =]` | create |

## 1.3 `src/Init/Data/List/Lemmas.lean`

### `headV` (4 create + 5 annotate)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `headV_map` | `head_map` | `@[simp]` | create |
| `headV_filterMap_of_eq_some` | `head_filterMap_of_eq_some` | none | create |
| `headV_tail` | `head_tail` | `@[simp]` | create |
| `cons_headV_tail` | `cons_head_tail` | `@[simp, grind =]` | create |
| `headV_mem` | `head_mem` | `@[simp]` | annotate |
| `headV_append_of_ne_nil` | `head_append_of_ne_nil` | `@[simp, grind =]` | annotate |
| `headV_append` | `head_append` | `@[grind =]` | annotate |
| `headV_replicate` | `head_replicate` | `@[simp]` | annotate |
| `headV_reverse` | `head_reverse` | `@[simp, grind =]` | annotate |

### `getLastV` (2 create + 7 annotate)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getLastV_map` | `getLast_map` | `@[simp]` | create |
| `getLastV_tail` | `getLast_tail` | `@[simp, grind =]` | create |
| `getLastV_cons_cons` | `getLast_cons_cons` | `@[simp, grind =]` | annotate |
| `getLastV_singleton` | `getLast_singleton` | `@[simp, grind =]` | annotate |
| `getLastV_mem` | `getLast_mem` | `@[simp]` | annotate |
| `getLastV_append_of_ne_nil` | `getLast_append_of_ne_nil` | `@[simp]` | annotate |
| `getLastV_append` | `getLast_append` | `@[grind =]` | annotate |
| `getLastV_replicate` | `getLast_replicate` | `@[simp]` | annotate |
| `getLastV_reverse` | `getLast_reverse` | `@[simp, grind =]` | annotate |

### `getElemV` (3 create)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getElemV_singleton` | `getElem_singleton` (line 300) | `@[simp]` | create |
| `getElemV_map` | `getElem_map` (line 1344) | `@[simp, grind =]` | create |
| `getElemV_append` | `getElem_append` (line 1866) | `@[grind =]` | create |

## 1.4 `src/Init/Data/List/Nat/Modify.lean` — `getElemV` (5 create)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getElemV_modifyHead_zero` | `getElem_modifyHead_zero` (line 49) | `@[simp]` | create |
| `getElemV_modifyHead_succ` | `getElem_modifyHead_succ` (line 52) | `@[simp]` | create |
| `getElemV_modify` | `getElem_modify` (line 208) | `@[grind =]` | create |
| `getElemV_modify_eq` | `getElem_modify_eq` (line 215) | `@[simp]` | create |
| `getElemV_modify_ne` | `getElem_modify_ne` (line 218) | `@[simp]` | create |

## 1.5 `src/Init/Data/List/Nat/Basic.lean` — `getElemV` (2 create)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getElemV_intersperse_two_mul` | `getElem_intersperse_two_mul` (line 160) | `@[simp]` | create |
| `getElemV_intersperse_two_mul_add_one` | `getElem_intersperse_two_mul_add_one` (line 165) | `@[simp]` | create |

## 1.6 `src/Init/Data/Option/Lemmas.lean` — `getV` (10-15 create)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getV_bind` | `get_bind` | `@[simp, grind =]` | create |
| `getV_map` | `get_map` | `@[simp, grind =]` | create |
| `getV_join` | `get_join` | `@[grind =]` | create |
| `getV_guard` | `get_guard` | `@[simp, grind =]` | create |
| `getV_dite` | `get_dite` | `@[simp]` | create |
| `getV_ite` | `get_ite` | `@[simp]` | create |
| `getV_dite'` | `get_dite'` | `@[simp]` | create |
| `getV_ite'` | `get_ite'` | `@[simp]` | create |
| `getV_filter` | `get_filter` | `@[simp, grind =]` | create |
| `getV_pfilter` | `get_pfilter` | `@[simp, grind =]` | create |

The following also had annotations removed in 5a80909. Check during implementation
whether V variants are appropriate (dependent types / special typeclasses):

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getV_none_eq_iff_true` | `get_none_eq_iff_true` | `@[simp]` | create (if applicable) |
| `getV_merge` | `get_merge` | `@[simp]` | create (if applicable) |
| `getV_pbind` | `get_pbind` | `@[simp, grind =]` | create (if applicable) |
| `getV_pmap` | `get_pmap` | `@[simp, grind =]` | create (if applicable) |
| `getV_min` | `get_min` | `@[simp, grind =]` | create (if applicable) |

## 1.7 `src/Init/Data/List/Scan/Lemmas.lean` — Scan V lemmas (6 create)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `headV_scanl` | `head_scanl` | `@[simp]` | create |
| `headV_scanr` | `head_scanr` | `@[simp]` | create |
| `getLastV_scanl` | `getLast_scanl` | none | create |
| `getLastV_scanr` | `getLast_scanr` | `@[grind =]` | create |
| `getElemV_scanl` | `getElem_scanl` | `@[simp, grind =]` | create |
| `getElemV_scanr` | `getElem_scanr` | `@[simp, grind =]` | create |

## 1.8 `src/Init/Data/List/OfFn.lean`

List's `getElemV_ofFn` already exists with `@[simp, grind =]`. No changes needed.
(Array's `getElemV_ofFn` is listed in section 1.1.)

## Summary

| File | Creates | Annotates | Total |
|------|---------|-----------|-------|
| Array/Lemmas.lean | 31 (11 backV + 20 getElemV) | 0 | 31 |
| Array/MapIdx.lean | 1 | 0 | 1 |
| Vector/Lemmas.lean | 34 (10 backV + 24 getElemV) | 0 | 34 |
| List/Lemmas.lean | 9 (4 headV + 2 getLastV + 3 getElemV) | 12 (5 headV + 7 getLastV) | 21 |
| List/Nat/Modify.lean | 5 | 0 | 5 |
| List/Nat/Basic.lean | 2 | 0 | 2 |
| Option/Lemmas.lean | 10-15 | 0 | 10-15 |
| List/Scan/Lemmas.lean | 6 | 0 | 6 |
| **Total** | **~98-103** | **12** | **~110-115** |
