# Step 2: Std V Lemma Parity

Status: good; Refinement Needed: no

## Goal
Achieve full lemma parity for Std collection types and fix annotation gaps.

All tables use unified format (same as Step 1):
- **V lemma**: the V variant to create or annotate
- **Proof-taking counterpart**: the proof-taking lemma it mirrors
- **Annotation**: the annotation the V lemma must have
- **Action**: `create`, `annotate`

## 2.1 TreeSet — no changes needed

Already complete:
- `getV`: 37 lemmas (bundled), 33 (raw)
- `minV`: 24 lemmas, `maxV`: 23 lemmas
- `atIdxV`, `getGEV/GTV/LEV/LTV`: at parity (non-V also has only bridge + congruence)

## 2.2 `src/Std/Data/TreeMap/Lemmas.lean` — `maxKeyV` (7 create)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `maxKeyV_eq_get_maxKey?` | `maxKey_eq_get_maxKey?` (line 4202) | none | create |
| `maxKeyV_eq_iff_getKey?_eq_self_and_forall` | `maxKey_eq_iff_getKey?_eq_self_and_forall` (line 4210) | none | create |
| `maxKeyV_eq_iff_mem_and_forall` | `maxKey_eq_iff_mem_and_forall` (line 4214) | none | create |
| `maxKeyV_erase_eq_iff_not_compare_eq_maxKeyV` | `maxKey_erase_eq_iff_not_compare_eq_maxKey` (line 4273) | none | create |
| `maxKeyV_eq_getLast_keys` | `maxKey_eq_getLast_keys` (line 4304) | none | create |
| `maxKeyV_eq_back_keysArray` | `maxKey_eq_back_keysArray` (line 4308) | none | create |
| `maxKeyV_modify` | `maxKey_modify` (line 4312) | none | create |

Other TreeMap operations (`minEntryV/maxEntryV`, `entryAtIdxV/keyAtIdxV`, range queries):
at parity — non-V also has only bridge + congruence lemmas.

**Detailed sub-plan**: [step-02/PLAN.md](step-02/PLAN.md)

## 2.3 `src/Std/Data/DTreeMap/Lemmas.lean` — `maxKeyV` (7 create)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `maxKeyV_eq_get_maxKey?` | `maxKey_eq_get_maxKey?` (line 5854) | none | create |
| `maxKeyV_eq_iff_getKey?_eq_self_and_forall` | `maxKey_eq_iff_getKey?_eq_self_and_forall` (line 5863) | none | create |
| `maxKeyV_eq_iff_mem_and_forall` | `maxKey_eq_iff_mem_and_forall` (line 5867) | none | create |
| `maxKeyV_erase_eq_iff_not_compare_eq_maxKeyV` | `maxKey_erase_eq_iff_not_compare_eq_maxKey` (line 5926) | none | create |
| `maxKeyV_eq_getLast_keys` | `maxKey_eq_getLast_keys` (line 5957) | none | create |
| `maxKeyV_eq_back_keysArray` | `maxKey_eq_back_keysArray` (line 5961) | none | create |
| `maxKeyV_modify` | `maxKey_modify` (line 5978) | none | create |

**Detailed sub-plan**: [step-03/PLAN.md](step-03/PLAN.md)

## 2.4 `src/Std/Data/DTreeMap/Raw/Lemmas.lean` (3 annotate)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getKeyV_insert` | `getKeyD_insert` (has @[grind =]) | `@[grind =]` | annotate |
| `getKeyV_erase` | `getKeyD_erase` (has @[grind =]) | `@[grind =]` | annotate |
| `getKeyV_insertIfNew` | `getKeyD_insertIfNew` (has @[grind =]) | `@[grind =]` | annotate |

**Detailed sub-plan**: [step-04/PLAN.md](step-04/PLAN.md)

## 2.5 `src/Std/Data/HashMap/Lemmas.lean` (2 create + 3 annotate)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getV_eq_getElem` | `get_eq_getElem` | `@[simp, grind =]` | create |
| `getV_getElem?` | `get_getElem?` | `@[grind =]` | create |
| `getKeyV_eq` | `getKey_eq` | `@[simp, grind =]` | annotate |
| `getKeyV_inter` | `getKey_inter` | `@[simp]` | annotate |
| `getKeyV_diff` | `getKey_diff` | `@[simp]` | annotate |

**Detailed sub-plan**: [step-05/PLAN.md](step-05/PLAN.md)

## 2.6 `src/Std/Data/HashMap/RawLemmas.lean` (2 create + 2 annotate)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getV_eq_getElem` | `get_eq_getElem` | `@[simp, grind =]` | create |
| `getV_getElem?` | `get_getElem?` | `@[grind =]` | create |
| `getKeyV_inter` | `getKey_inter` | `@[simp]` | annotate |
| `getKeyV_diff` | `getKey_diff` | `@[simp]` | annotate |

**Detailed sub-plan**: [step-06/PLAN.md](step-06/PLAN.md)

## 2.7 `src/Std/Data/DHashMap/Lemmas.lean` (4 create + 3 annotate)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getV_eq_getElem` | `get_eq_getElem` (dep + const) | `@[simp, grind =]` | create |
| `getV_getElem?` | `get_getElem?` (dep + const) | `@[grind =]` | create |
| `getKeyV_eq` | `getKey_eq` | `@[simp, grind =]` | annotate |
| `getKeyV_inter` | `getKey_inter` | `@[simp]` | annotate |
| `getKeyV_diff` | `getKey_diff` | `@[simp]` | annotate |

**Detailed sub-plan**: [step-07/PLAN.md](step-07/PLAN.md)

## 2.8 `src/Std/Data/DHashMap/RawLemmas.lean` (4 create + 3 annotate) — same pattern as 2.7

`getEntryV`: defined but zero public `getEntry` lemmas exist in DHashMap, so parity
holds trivially.

**Detailed sub-plan**: [step-08/PLAN.md](step-08/PLAN.md)

## 2.9 Ext types — annotation additions only

### `src/Std/Data/ExtTreeMap/Lemmas.lean` (3 annotate)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getKeyV_insert` | `getKeyD_insert` | `@[grind =]` | annotate |
| `getKeyV_erase` | `getKeyD_erase` | `@[grind =]` | annotate |
| `getKeyV_insertIfNew` | `getKeyD_insertIfNew` | `@[grind =]` | annotate |

### `src/Std/Data/ExtHashMap/Lemmas.lean` (9 annotate)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getKeyV_insert` | `getKeyD_insert` | `@[grind =]` | annotate |
| `getKeyV_erase` | `getKeyD_erase` | `@[grind =]` | annotate |
| `getKeyV_insertIfNew` | `getKeyD_insertIfNew` | `@[grind =]` | annotate |
| `getKeyV_alter` | `getKeyD_alter` | `@[grind =]` | annotate |
| `getElemV_modify` | `getElemD_modify` | `@[grind =]` | annotate |
| `getKeyV_modify` | `getKeyD_modify` | `@[grind =]` | annotate |
| `getElemV_filterMap` | `getElemD_filterMap` | `@[grind =]` | annotate |
| `getKeyV_filterMap` | `getKeyD_filterMap` | `@[grind =]` | annotate |
| `getKeyV_filter` | `getKeyD_filter` | `@[grind =]` | annotate |

### `src/Std/Data/ExtDHashMap/Lemmas.lean` (3 annotate)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getKeyV_insert` | `getKeyD_insert` | `@[grind =]` | annotate |
| `getKeyV_erase` | `getKeyD_erase` | `@[grind =]` | annotate |
| `getKeyV_insertIfNew` | `getKeyD_insertIfNew` | `@[grind =]` | annotate |

### `src/Std/Data/ExtDTreeMap/Lemmas.lean` (3 annotate)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getKeyV_insert` | `getKeyD_insert` | `@[grind =]` | annotate |
| `getKeyV_erase` | `getKeyD_erase` | `@[grind =]` | annotate |
| `getKeyV_insertIfNew` | `getKeyD_insertIfNew` | `@[grind =]` | annotate |

ExtTreeSet, ExtHashSet: already complete — no changes needed.

**Detailed sub-plan**: [step-09/PLAN.md](step-09/PLAN.md)

## Summary

| File | Creates | Annotates | Total |
|------|---------|-----------|-------|
| TreeMap/Lemmas.lean | 7 | 0 | 7 |
| DTreeMap/Lemmas.lean | 7 | 0 | 7 |
| DTreeMap/Raw/Lemmas.lean | 0 | 3 | 3 |
| HashMap/Lemmas.lean | 2 | 3 | 5 |
| HashMap/RawLemmas.lean | 2 | 2 | 4 |
| DHashMap/Lemmas.lean | 4 (2 dep + 2 Const) | 3 | 7 |
| DHashMap/RawLemmas.lean | 4 (2 dep + 2 Const) | 3 | 7 |
| ExtTreeMap/Lemmas.lean | 0 | 3 | 3 |
| ExtHashMap/Lemmas.lean | 0 | 9 | 9 |
| ExtDHashMap/Lemmas.lean | 0 | 3 | 3 |
| ExtDTreeMap/Lemmas.lean | 0 | 3 | 3 |
| **Total** | **~26** | **~32** | **~58** |
