# Step 3b.2: HashMap V Lemma Parity (Remaining)

Status: good; Refinement Needed: no

## Files

`src/Std/Data/HashMap/Lemmas.lean`, `src/Std/Data/HashMap/RawLemmas.lean`

## Audit results

### FALSE POSITIVE — V variant already exists

The following candidates from the stub already have V variants in both Lemmas.lean
and RawLemmas.lean:

| Candidate | Existing V variant | Notes |
|-----------|--------------------|-------|
| `get_eq_getElem` | `getV_eq_getElem` | **ALREADY PLANNED** in Step 2.5/2.6 |
| `getElem_insert` | `getElemV_insert` | `@[grind =]` already present |
| `getElem_erase` | `getElemV_erase` | `@[grind =]` already present |
| `getElem_eq_getD` | `getElemV_eq_getD_getElem?` | Exists (different name convention but equivalent) |
| `getV_eq_getElem` | — | Already exists; was listed as candidate but is itself a V lemma. **ALREADY PLANNED** in Step 2.5/2.6 |
| `getElem_insertIfNew` | `getElemV_insertIfNew` | `@[grind =]` already present |
| `getElem_union_of_mem_right` | `getElemV_union` + `getElemV_union_of_not_mem_right` | Full V coverage exists |
| `getElem_inter` | `getElemV_inter` | `@[grind =]` already present |
| `getElem_diff` | `getElemV_diff` | `@[grind =]` already present |

**Result: 9 of 17 candidates per file are FALSE POSITIVE.** No action needed.

### NOT MEANINGFUL — any/all iff lemmas (8 per file)

The remaining 8 candidates are the any/all iff lemmas:

| Lemma | Statement pattern |
|-------|-------------------|
| `any_eq_true_iff_exists_mem_getKey_getElem` | `m.any p = true ↔ ∃ (a : α) (h : a ∈ m), p (m.getKey a h) (m[a]'h)` |
| `any_eq_true_iff_exists_mem_getElem` | `m.any p = true ↔ ∃ (a : α) (h : a ∈ m), p a (m[a]'h)` |
| `any_eq_false_iff_forall_mem_getKey_getElem` | `m.any p = false ↔ ∀ (a : α) (h : a ∈ m), p (m.getKey a h) (m[a]'h) = false` |
| `any_eq_false_iff_forall_mem_getElem` | `m.any p = false ↔ ∀ (a : α) (h : a ∈ m), p a (m[a]'h) = false` |
| `all_eq_true_iff_forall_mem_getKey_getElem` | `m.all p = true ↔ ∀ (a : α) (h : a ∈ m), p (m.getKey a h) (m[a]'h)` |
| `all_eq_true_iff_forall_mem_getElem` | `m.all p = true ↔ ∀ (a : α) (h : a ∈ m), p a (m[a]'h)` |
| `all_eq_false_iff_exists_mem_getKey_getElem` | `m.all p = false ↔ ∃ (a : α) (h : a ∈ m), p (m.getKey a h) (m[a]'h) = false` |
| `all_eq_false_iff_exists_mem_getElem` | `m.all p = false ↔ ∃ (a : α) (h : a ∈ m), p a (m[a]'h) = false` |

**Analysis:** In all 8 lemmas, `m[a]'h` appears under a quantifier (`∃` or `∀`) where
`h : a ∈ m` is a bound variable. A V variant would replace `m[a]'h` with `m｢a｣` but
the membership proof `h` is still required by the quantifier structure itself
(`∃ (a : α) (h : a ∈ m), ...` or `∀ (a : α) (h : a ∈ m), ...`).

For the `getKey` variants, `m.getKey a h` would also need to become `m.getKeyV a`,
but again `h : a ∈ m` remains as a bound variable in the quantifier.

The resulting V variants would be:
```
∃ (a : α), a ∈ m ∧ p (m.getKeyV a) (m｢a｣)
∀ (a : α), a ∈ m → p (m.getKeyV a) (m｢a｣)
```
etc. These are **not mechanical substitutions** — they change the quantifier structure
(from `∃ (a) (h : a ∈ m), ...` to `∃ a, a ∈ m ∧ ...` since the proof is no longer
used in the body). However, they provide **no practical benefit**:

1. The proof `h : a ∈ m` is inherently present in the quantifier — V's purpose of
   avoiding proof obligations is not served when the proof is a bound variable.
2. These lemmas are not used with `simp` or `grind` — they are characterization lemmas
   used for manual reasoning, where binding `h` directly is more convenient.
3. No other collection type (DTreeMap, TreeMap, etc.) has V variants of its any/all
   characterization lemmas.

**Result: 8 candidates per file are NOT MEANINGFUL.** No action needed.

## Summary

All 17 candidates in each file are either false positives (V variant exists) or
not meaningful (any/all iff lemmas under quantifiers). The 2 candidates that were
already planned (`getV_eq_getElem`, `getV_getElem?`) are covered by Step 2.5/2.6.

**No new lemmas to create in this step.** This step is empty.
