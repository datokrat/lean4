# Step 3b.4: DTreeMap + HashSet V Lemma Parity (Remaining)

Status: good; Refinement Needed: no

## Files

`src/Std/Data/DTreeMap/Internal/Lemmas.lean`,
`src/Std/Data/DTreeMap/Lemmas.lean`,
`src/Std/Data/DTreeMap/Internal/WF/Lemmas.lean`,
`src/Std/Data/HashSet/RawLemmas.lean`

## Analysis

### DTreeMap/Internal/Lemmas.lean — `minKey_eq_getElem_keysArray` (line 7990)

**FALSE POSITIVE (Internal-only).**
This lemma relates the Internal `Impl.minKey` to `Impl.keysArray[0]'(...)`. The
`Impl` module does not define `minKeyV` — V operations are only defined on the
public `DTreeMap` and `DTreeMap.Raw` types. Creating a V variant here is not
meaningful. The public V coverage should come from `DTreeMap/Lemmas.lean` (see
next entry).

### DTreeMap/Lemmas.lean — `minKey_eq_getElem_keysArray` (line 5132)

**Confirmed gap — needs V variant.**

The proof-taking lemma is:
```
theorem minKey_eq_getElem_keysArray [TransCmp cmp] {he} :
    t.minKey he = t.keysArray[0]'(...)
```
The V variant mirrors what TreeMap.Raw already has at line 3951 of
`src/Std/Data/TreeMap/Raw/Lemmas.lean` (`minKeyV_eq_getElemV_keysArray`).

In addition, the companion lemma `minKeyV_eq_headV_keys` is also missing.
TreeMap.Raw has it at line 3945 with `@[grind =_]`.

**New lemmas (2 create):**

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `minKeyV_eq_headV_keys` | `minKey_eq_head_keys` (line 5128) | `@[grind =_]` | create |
| `minKeyV_eq_getElemV_keysArray` | `minKey_eq_getElem_keysArray` (line 5132) | none | create |

**Suggested signatures:**

```lean
@[grind =_] theorem minKeyV_eq_headV_keys [TransCmp cmp] {_ : Nonempty α} :
    t.minKeyV = t.keys.headV := by
  rw [List.headV_eq_getElemV, List.getElemV_eq_getElem?_getD, ← List.head?_eq_getElem?,
      ← List.headD_eq_head?_getD]
  simpa [DTreeMap.minKeyV] using minKeyD_eq_headD_keys

theorem minKeyV_eq_getElemV_keysArray [TransCmp cmp] {_ : Nonempty α} :
    t.minKeyV = t.keysArray｢0｣ := by
  rw [Array.getElemV_eq_getD]; simpa [DTreeMap.minKeyV] using minKeyD_eq_getD_keysArray
```

Note: these follow the exact same proof pattern as
`src/Std/Data/TreeMap/Raw/Lemmas.lean` lines 3945–3953.

### DTreeMap/Internal/WF/Lemmas.lean — `entryAtIdx_eq_getElem` (line 2366), `keyAtIdx_eq_getElem_fst` (line 2385), Const `entryAtIdx_eq_getElem` (line 2405)

**FALSE POSITIVE (Internal-only).**

These lemmas exist in the `Std.DTreeMap.Internal.Impl` namespace and relate
internal operations (`Impl.entryAtIdx`, `Impl.keyAtIdx`) to `Impl.toListModel`.
The Internal module does not define V operations — `entryAtIdxV` and
`keyAtIdxV` are only defined on the public `DTreeMap` and `DTreeMap.Raw` types.

At the public level, the bridge lemmas `entryAtIdx_eq_entryAtIdxV` (line 6487)
and `keyAtIdx_eq_keyAtIdxV` (line 6497) already exist. There are no public
`entryAtIdx_eq_getElem`-style lemmas (they don't reference `toListModel` at the
public level), so there is nothing to create V variants of.

### HashSet/RawLemmas.lean — `all_eq_false_iff_exists_mem_getElem` (line 719)

**FALSE POSITIVE (not a V-variant candidate).**

This lemma's name contains `getElem` but it does NOT use a proof-taking
`getElem` operation that needs a V variant. With `[LawfulBEq α]`, it
simplifies the quantifier to `∃ (a : α), a ∈ m ∧ p a = false` — there is no
`get`/`getElem` call in the statement at all.

The related lemma `all_eq_false_iff_exists_mem_get` (line 714) does use the
proof-taking `m.get a h`, but a V variant (`all_eq_false_iff_exists_mem_getV`)
would not follow standard patterns: no other collection type has such a lemma,
and the existential already provides the membership witness. This would be a
new pattern, not parity. Skipping.

## Summary

| File | Creates | Annotates | Total |
|------|---------|-----------|-------|
| DTreeMap/Lemmas.lean | 2 | 0 | 2 |
| DTreeMap/Internal/Lemmas.lean | 0 (false positive) | 0 | 0 |
| DTreeMap/Internal/WF/Lemmas.lean | 0 (false positive) | 0 | 0 |
| HashSet/RawLemmas.lean | 0 (false positive) | 0 | 0 |
| **Total** | **2** | **0** | **2** |

## Implementation order

1. Add `minKeyV_eq_headV_keys` with `@[grind =_]` annotation
2. Add `minKeyV_eq_getElemV_keysArray` immediately after
3. Both go in `src/Std/Data/DTreeMap/Lemmas.lean`, near the existing `minKeyV`
   lemma block (around line 5598, after `minKeyV_modify`)

## Notes

- The DTreeMap.Raw counterpart (`src/Std/Data/DTreeMap/Raw/Lemmas.lean`) should
  also get the same two lemmas. Check whether it already has `minKeyD_eq_headD_keys`
  and `minKeyD_eq_getD_keysArray` as proof bases (it does — lines 5516–5518).
