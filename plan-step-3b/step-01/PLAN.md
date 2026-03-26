# Step 3b.1: TreeMap V Lemma Parity (Remaining)

Status: good; Refinement Needed: no

## Files

`src/Std/Data/TreeMap/Lemmas.lean`, `src/Std/Data/TreeMap/Raw/Lemmas.lean`

## Audit results

### `TreeMap/Lemmas.lean` — 8 candidates audited

| # | Candidate | Expected V name | Result |
|---|-----------|----------------|--------|
| 1 | `getElem_insert` (line 292) | `getElemV_insert` | **FALSE POSITIVE** — exists at line 413 |
| 2 | `getElem_erase` (line 316) | `getElemV_erase` | **FALSE POSITIVE** — exists at line 450 |
| 3 | `getElem_eq_getD` (line 480) | `getElemV_eq_getD` | **FALSE POSITIVE** — exists as `getElemV_eq_getD_getElem?` at line 476 |
| 4 | `getElem_insertIfNew` (line 867) | `getElemV_insertIfNew` | **CONFIRMED GAP** |
| 5 | `getElem_union_of_mem_right` (line 1969) | `getElemV_union_of_mem_right` | **CONFIRMED GAP** (see notes) |
| 6 | `getElem_inter` (line 2269) | `getElemV_inter` | **FALSE POSITIVE** — exists at line 2303 |
| 7 | `getElem_diff` (line 2610) | `getElemV_diff` | **FALSE POSITIVE** — exists at line 2644 |
| 8 | `minKey_eq_getElem_keysArray` (line 3559) | `minKeyV_eq_getElemV_keysArray` | **CONFIRMED GAP** |

### `TreeMap/Raw/Lemmas.lean` — 8 candidates audited

| # | Candidate | Expected V name | Result |
|---|-----------|----------------|--------|
| 1 | `getElem_insert` (line 287) | `getElemV_insert` | **FALSE POSITIVE** — exists at line 410 |
| 2 | `getElem_erase` (line 313) | `getElemV_erase` | **FALSE POSITIVE** — exists at line 448 |
| 3 | `getElem_eq_getD` (line 481) | `getElemV_eq_getD` | **FALSE POSITIVE** — exists as `getElemV_eq_getD_getElem?` at line 477 |
| 4 | `getElem_insertIfNew` (line 879) | `getElemV_insertIfNew` | **FALSE POSITIVE** — exists at line 896 |
| 5 | `getElem_insertMany_list` (line 1385) | `getElemV_insertMany_list` | **FALSE POSITIVE** — exists at line 1447 |
| 6 | `getElem_union_of_mem_right` (line 2022) | `getElemV_union_of_mem_right` | **CONFIRMED GAP** (see notes) |
| 7 | `getElem_inter` (line 2336) | `getElemV_inter` | **FALSE POSITIVE** — exists at line 2371 |
| 8 | `getElem_diff` (line 2690) | `getElemV_diff` | **FALSE POSITIVE** — exists at line 2725 |

### Cross-reference with Step 2.2

Step 2.2 covers only `maxKeyV` lemmas (7 creates). None of the confirmed gaps here overlap.

## Confirmed gaps — signatures and actions

### Gap 1: `getElemV_insertIfNew` in `TreeMap/Lemmas.lean`

**Proof-taking counterpart** (line 867):
```lean
theorem getElem_insertIfNew [TransCmp cmp] {k a : α} {v : β} {h₁} :
    (t.insertIfNew k v)[a]'h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then v else t[a]'(mem_of_mem_insertIfNew' h₁ h₂)
```

**Existing `!` variant** (line 872):
```lean
@[grind =] theorem getElem!_insertIfNew [TransCmp cmp] [Inhabited β] {k a : α} {v : β} :
    (t.insertIfNew k v)[a]! = if cmp k a = .eq ∧ ¬ k ∈ t then v else t[a]!
```

**V signature to create** (place after line 874, near `getD_insertIfNew`):
```lean
@[grind =] theorem getElemV_insertIfNew [TransCmp cmp] {_ : Nonempty β} {k a : α} {v : β} :
    (t.insertIfNew k v)｢a｣ =
      if cmp k a = .eq ∧ ¬ k ∈ t then v else t｢a｣ :=
  DTreeMap.Const.getV_insertIfNew
```

**Annotation**: `@[grind =]` (matches `getElem!_insertIfNew` and `getD_insertIfNew`)

**Delegate exists**: `DTreeMap.Const.getV_insertIfNew` at `src/Std/Data/DTreeMap/Lemmas.lean` line 1232.

---

### Gap 2: `getElemV_union_of_mem_right` in `TreeMap/Lemmas.lean`

**Proof-taking counterpart** (line 1969):
```lean
theorem getElem_union_of_mem_right [TransCmp cmp]
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∪ t₂)[k]'(mem_union_of_right mem) = t₂[k]'mem
```

**V signature to create** (place after line 2033, after `getElemV_union_of_not_mem_right`):
```lean
theorem getElemV_union_of_mem_right [TransCmp cmp] {_ : Nonempty β}
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∪ t₂)｢k｣ = t₂｢k｣ := by
  simp [getElemV_union, getD_eq_getElem_of_mem mem]
```

**Annotation**: none (mirrors `getElem_union_of_mem_right` which has no annotation)

**Note**: No DTreeMap.Const delegate exists. The `get!`/`getD` `_of_mem_right` variants are also missing throughout
the stack. This lemma needs a direct proof. The proof should follow from `getElemV_union` (which states
`(t₁ ∪ t₂)｢k｣ = t₂.getD k (t₁｢k｣)`) and the fact that `getD` on a present key equals `getElem`. If the
necessary simplification lemma (`getD_eq_getElem_of_mem` or similar) does not exist, this may need a
slightly more involved proof. Flag for verification at implementation time.

---

### Gap 3: `getElemV_union_of_mem_right` in `TreeMap/Raw/Lemmas.lean`

**Proof-taking counterpart** (line 2022):
```lean
theorem getElem_union_of_mem_right [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∪ t₂)[k]'(mem_union_of_right h₁ h₂ mem) = t₂[k]'mem
```

**V signature to create** (place after line 2086, after `getElemV_union_of_not_mem_right`):
```lean
theorem getElemV_union_of_mem_right [TransCmp cmp] {_ : Nonempty β} (h₁ : t₁.WF) (h₂ : t₂.WF)
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∪ t₂)｢k｣ = t₂｢k｣ := by
  simp [getElemV_union h₁ h₂, getD_eq_getElem_of_mem h₂ mem]
```

**Annotation**: none

**Note**: Same situation as Gap 2 — no DTreeMap delegate. Proof needs direct construction via
`getElemV_union` plus simplification. The `h₁` and `h₂` (WF) proofs are needed since this is the Raw variant.

---

### Gap 4: `minKeyV_eq_getElemV_keysArray` in `TreeMap/Lemmas.lean`

**Proof-taking counterpart** (line 3559):
```lean
theorem minKey_eq_getElem_keysArray [TransCmp cmp] {he} :
    t.minKey he = t.keysArray[0]'(Nat.zero_lt_of_ne_zero (by simpa [...] using he))
```

**Existing Raw counterpart** (`Raw/Lemmas.lean` line 3951):
```lean
theorem minKeyV_eq_getElemV_keysArray [TransCmp cmp] [Nonempty α] (h : t.WF) :
    t.minKeyV = t.keysArray｢0｣
```

**V signature to create** (place near line 3561, after `minKey_eq_getElem_keysArray`):
```lean
theorem minKeyV_eq_getElemV_keysArray [TransCmp cmp] {_ : Nonempty α} :
    t.minKeyV = t.keysArray｢0｣ := by
  rw [Array.getElemV_eq_getD]; simpa [TreeMap.minKeyV] using minKeyD_eq_getD_keysArray
```

**Annotation**: none (mirrors `minKey_eq_getElem_keysArray` which has no annotation)

**Note**: No DTreeMap delegate. Direct proof following the pattern from `Raw/Lemmas.lean` line 3951-3953.
The bundled variant does not need a `WF` proof.

## Summary

| File | Confirmed gaps | False positives |
|------|---------------|-----------------|
| `TreeMap/Lemmas.lean` | 3 (getElemV_insertIfNew, getElemV_union_of_mem_right, minKeyV_eq_getElemV_keysArray) | 5 |
| `TreeMap/Raw/Lemmas.lean` | 1 (getElemV_union_of_mem_right) | 7 |
| **Total** | **4 create** | **12** |

## Implementation notes

1. `getElemV_insertIfNew` (bundled) is straightforward — delegates to existing `DTreeMap.Const.getV_insertIfNew`.
2. `getElemV_union_of_mem_right` (both files) has no DTreeMap delegate and `get!`/`getD` `_of_mem_right` are also absent throughout the stack. The proof must be constructed directly from `getElemV_union` + the fact that `getD` on a present key returns the stored value. Verify the exact proof term at implementation time.
3. `minKeyV_eq_getElemV_keysArray` (bundled) follows the Raw file's proof pattern.
4. Per SIGNATURE_SPEC.md, use `{_ : Nonempty β}` (or `{_ : Nonempty α}`) instead of `[Nonempty β]` since these are used by `rw`/`simp` and the instance is inferred by unification.
