# Step 2.2: TreeMap/Lemmas.lean — maxKeyV (7 create)

Status: not started

## File

`src/Std/Data/TreeMap/Lemmas.lean`

## Context

`maxKeyV` is defined as `t.maxKeyD Classical.ofNonempty` and requires `{_ : Nonempty α}` instead of
`h : t.isEmpty = false`. Several `maxKeyV_*` lemmas already exist (insert, insertIfNew, mem, le,
erase_eq_of_not_compare, modify, alter, etc.). The 7 below are missing V variants of their
proof-taking counterparts.

Existing pattern: V lemmas are proved via `simpa [TreeMap.maxKeyV] using maxKeyD_<name>` (reducing
to the D variant). The D variant has a `fallback` parameter; the V variant fixes
`fallback := Classical.ofNonempty`.

## Lemmas to create

| # | V lemma | Counterpart | Annotation | Suggested signature |
|---|---------|-------------|------------|---------------------|
| 1 | `maxKeyV_eq_get_maxKey?` | `maxKey_eq_get_maxKey?` (line 4202) | none | `theorem maxKeyV_eq_get_maxKey? [TransCmp cmp] {_ : Nonempty α} (he : t.isEmpty = false) : t.maxKeyV = t.maxKey?.get (isSome_maxKey?_iff_isEmpty_eq_false.mpr he)` |
| 2 | `maxKeyV_eq_iff_getKey?_eq_self_and_forall` | `maxKey_eq_iff_getKey?_eq_self_and_forall` (line 4210) | none | Already exists (line 4629). **Verify only; skip if present.** Signature: `theorem maxKeyV_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] {_ : Nonempty α} (he : t.isEmpty = false) {km} : t.maxKeyV = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp k km).isLE` |
| 3 | `maxKeyV_eq_iff_mem_and_forall` | `maxKey_eq_iff_mem_and_forall` (line 4214) | none | Already exists (line 4634). **Verify only; skip if present.** Signature: `theorem maxKeyV_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] {_ : Nonempty α} (he : t.isEmpty = false) {km} : t.maxKeyV = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp k km).isLE` |
| 4 | `maxKeyV_erase_eq_iff_not_compare_eq_maxKeyV` | `maxKey_erase_eq_iff_not_compare_eq_maxKey` (line 4273) | none | `theorem maxKeyV_erase_eq_iff_not_compare_eq_maxKeyV [TransCmp cmp] {_ : Nonempty α} {k} (he : (t.erase k).isEmpty = false) : (t.erase k).maxKeyV = t.maxKeyV ↔ ¬ cmp k t.maxKeyV = .eq` |
| 5 | `maxKeyV_eq_getLast_keys` | `maxKey_eq_getLast_keys` (line 4304) | none | `theorem maxKeyV_eq_getLast_keys [TransCmp cmp] {_ : Nonempty α} (he : t.isEmpty = false) : t.maxKeyV = t.keys.getLast (List.isEmpty_eq_false_iff.mp <| isEmpty_keys ▸ he)` |
| 6 | `maxKeyV_eq_back_keysArray` | `maxKey_eq_back_keysArray` (line 4308) | none | `theorem maxKeyV_eq_back_keysArray [TransCmp cmp] {_ : Nonempty α} (he : t.isEmpty = false) : t.maxKeyV = t.keysArray.back (Nat.zero_lt_of_ne_zero (by simpa [size_keysArray, isEmpty_eq_size_eq_zero, - Array.size_eq_zero_iff] using he))` |
| 7 | `maxKeyV_modify` | `maxKey_modify` (line 4312, Const namespace) | none | Already exists (line 4718, `@[grind =]`). **Verify only; skip if present.** Signature: `@[grind =] theorem maxKeyV_modify [TransCmp cmp] {_ : Nonempty α} {k f} (he : (modify t k f).isEmpty = false) : (modify t k f).maxKeyV = if cmp t.maxKeyV k = .eq then k else t.maxKeyV` |

## Notes

- Items 2, 3, and 7 appear to already exist. Verify during implementation and skip if confirmed.
- Items 1, 4, 5, 6 are the ones that truly need to be created (4 net new lemmas).
- Item 1 (`maxKeyV_eq_get_maxKey?`): the V variant still takes `he : t.isEmpty = false` because the RHS uses `maxKey?.get` which needs a proof of `isSome`. This is a bridge lemma connecting V and `?` forms.
- Item 4: the proof-taking counterpart uses `isEmpty_eq_false_of_isEmpty_erase_eq_false he` to thread the proof. The V variant avoids this by using `maxKeyV` on both sides, needing only `he` for the erase.
- Items 5 and 6: these connect `maxKeyV` to `keys.getLast` and `keysArray.back`. The Raw layer already has V variants using `getLastV`/`backV` (lines 4564, 4570), but the non-Raw TreeMap uses `getLast`/`back` with explicit proofs (matching the proof-taking counterpart style).
- Place new lemmas near the existing `maxKeyV_*` block (around lines 4625-4742).

## Proof strategy

All proofs should follow the existing pattern:
```lean
simpa [TreeMap.maxKeyV] using <D_variant_or_bridge_lemma>
```
or use `maxKey_eq_maxKeyV` to rewrite and apply the proof-taking counterpart.
