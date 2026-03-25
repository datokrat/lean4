# Step 2.3: DTreeMap/Lemmas.lean — maxKeyV (7 create)

Status: not started

## File

`src/Std/Data/DTreeMap/Lemmas.lean`

## Context

`maxKeyV` is defined as `t.maxKeyD Classical.ofNonempty` and requires `{_ : Nonempty α}` instead of
`h : t.isEmpty = false`. Several `maxKeyV_*` lemmas already exist in this file. The 7 below are
listed in the parent plan as missing V variants. Some already exist and should be verified only.

Existing pattern: V lemmas are proved via `simpa [DTreeMap.maxKeyV] using maxKeyD_<name>` or
`simpa [DTreeMap.maxKeyV] using Impl.<name> t.wf`.

Note: DTreeMap has both a dependent `modify` (top-level) and a `Const.modify`. The proof-taking
counterpart at line 5978 is `Const.maxKey_modify`. The V variant `Const.maxKeyV_modify` already
exists at line 6439. The top-level `maxKeyV_modify` (line 6422) also exists.

## Lemmas to create

| # | V lemma | Counterpart | Annotation | Suggested signature |
|---|---------|-------------|------------|---------------------|
| 1 | `maxKeyV_eq_get_maxKey?` | `maxKey_eq_get_maxKey?` (line 5854) | none | `theorem maxKeyV_eq_get_maxKey? [TransCmp cmp] {_ : Nonempty α} (he : t.isEmpty = false) : t.maxKeyV = t.maxKey?.get (isSome_maxKey?_iff_isEmpty_eq_false.mpr he)` |
| 2 | `maxKeyV_eq_iff_getKey?_eq_self_and_forall` | `maxKey_eq_iff_getKey?_eq_self_and_forall` (line 5863) | none | Already exists (line 6334). **Verify only; skip if present.** Signature: `theorem maxKeyV_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] {_ : Nonempty α} (he : t.isEmpty = false) {km} : t.maxKeyV = km ↔ t.getKey? km = some km ∧ ∀ k ∈ t, (cmp k km).isLE` |
| 3 | `maxKeyV_eq_iff_mem_and_forall` | `maxKey_eq_iff_mem_and_forall` (line 5867) | none | Already exists (line 6339). **Verify only; skip if present.** Signature: `theorem maxKeyV_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {_ : Nonempty α} (he : t.isEmpty = false) {km} : t.maxKeyV = km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp k km).isLE` |
| 4 | `maxKeyV_erase_eq_iff_not_compare_eq_maxKeyV` | `maxKey_erase_eq_iff_not_compare_eq_maxKey` (line 5926) | none | `theorem maxKeyV_erase_eq_iff_not_compare_eq_maxKeyV [TransCmp cmp] {_ : Nonempty α} {k} (he : (t.erase k).isEmpty = false) : (t.erase k).maxKeyV = t.maxKeyV ↔ ¬ cmp k t.maxKeyV = .eq` |
| 5 | `maxKeyV_eq_getLast_keys` | `maxKey_eq_getLast_keys` (line 5957) | none | `theorem maxKeyV_eq_getLast_keys [TransCmp cmp] {_ : Nonempty α} (he : t.isEmpty = false) : t.maxKeyV = t.keys.getLast (List.isEmpty_eq_false_iff.mp <| isEmpty_keys ▸ he)` |
| 6 | `maxKeyV_eq_back_keysArray` | `maxKey_eq_back_keysArray` (line 5961) | none | `theorem maxKeyV_eq_back_keysArray [TransCmp cmp] {_ : Nonempty α} (he : t.isEmpty = false) : t.maxKeyV = t.keysArray.back (Nat.zero_lt_of_ne_zero (by simpa [size_keysArray, isEmpty_eq_size_eq_zero, - Array.size_eq_zero_iff] using he))` |
| 7 | `Const.maxKeyV_modify` | `Const.maxKey_modify` (line 5978) | none | Already exists (line 6439, `@[grind =]`). **Verify only; skip if present.** Signature: `@[grind =] theorem maxKeyV_modify [TransCmp cmp] {_ : Nonempty α} {k f} (he : (modify t k f).isEmpty = false) : (modify t k f).maxKeyV = if cmp t.maxKeyV k = .eq then k else t.maxKeyV` |

## Notes

- Items 2, 3, and 7 appear to already exist. Verify during implementation and skip if confirmed.
- Items 1, 4, 5, 6 are the ones that truly need to be created (4 net new lemmas).
- Item 1 (`maxKeyV_eq_get_maxKey?`): bridge lemma connecting V and `?` forms. Still takes `he` for the `Option.get` on the RHS.
- Item 4: the `_iff_` form for V. The existing V variant `maxKeyV_erase_eq_of_not_compare_maxKeyV_eq` proves one direction (equality given the negated compare). This new lemma gives the biconditional.
- Items 5 and 6: connect `maxKeyV` to `keys.getLast` and `keysArray.back`. The Raw layer has V-specific versions using `getLastV`/`backV`, but DTreeMap uses `getLast`/`back` with explicit proofs.
- Place new lemmas near the existing `maxKeyV_*` block (around lines 6330-6462).
- Note `∀ k ∈ t` syntax in DTreeMap vs `∀ k, k ∈ t →` in TreeMap (DTreeMap uses anonymous membership).

## Proof strategy

All proofs should follow the existing pattern:
```lean
simpa [DTreeMap.maxKeyV] using maxKeyD_<name>
```
or rewrite via `maxKey_eq_maxKeyV` and apply the proof-taking counterpart.
For the `_iff_` erase lemma (item 4), may need to combine `maxKeyV_erase_eq_of_not_compare_maxKeyV_eq` with a converse direction, or derive from the D version.
