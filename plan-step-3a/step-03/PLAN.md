# Step 3a.3: List V Lemma Parity (Remaining)

Status: good; Refinement Needed: no

## Files

Multiple files under `src/Init/Data/List/`.

## Summary of audit

Most candidates from the original stub are either:
- **FALSE POSITIVE**: A V variant already exists.
- **ALREADY PLANNED**: Covered by Step 1.3, 1.4, 1.5, or 1.7.
- **NOT APPLICABLE**: The lemma is a "bridge" between proof-taking forms, a quantified statement,
  or an internal helper where a V variant is not meaningful.

Below is the disposition of every candidate, followed by the table of confirmed gaps.

---

## Disposition of all candidates

### `Attach.lean`

| Lemma | Disposition | Notes |
|-------|-------------|-------|
| `getElem_pmap` (line 250) | **CANDIDATE** | See confirmed gaps below. The V variant retains `hn : i < l.length` (needed for the proof term of `f`'s argument and for `Nonempty` witness), but replaces `[i]'proof` with `｢i｣` on both sides. |
| `getElem_attachWith` (line 275) | **CANDIDATE** | Same pattern — retains `h : i < xs.length`, replaces indexing with `getElemV`. |
| `getElem_attach` (line 281) | **CANDIDATE** | Same pattern. |

### `Count.lean`

| Lemma | Disposition | Notes |
|-------|-------------|-------|
| `boole_getElem_le_countP` (line 129) | NOT APPLICABLE | This is an inequality `(if p l[i] then 1 else 0) ≤ l.countP p`. The `h : i < l.length` proof is needed to make `l[i]` well-defined, and the inequality is only meaningful when `i` is in-bounds. A V variant with `l｢i｣` would make the statement vacuously true when out-of-bounds (since `l｢i｣` returns garbage), which is not useful. |
| `boole_getElem_le_count` (line 319) | NOT APPLICABLE | Same reasoning as `boole_getElem_le_countP`. |

### `Find.lean`

| Lemma | Disposition | Notes |
|-------|-------------|-------|
| `findIdx_getElem` (line 569) | NOT APPLICABLE | Statement is `p xs[xs.findIdx p]` where the proof `w : xs.findIdx p < xs.length` is needed for correctness. A V variant `p xs｢xs.findIdx p｣` would be vacuously true when `findIdx` returns an out-of-bounds index (since `xs｢...｣` is garbage and `p garbage` could be anything). Not useful. |

### `MapIdx.lean`

| Lemma | Disposition | Notes |
|-------|-------------|-------|
| `getElem_mapFinIdx_go` (line 116) | NOT APPLICABLE | Internal helper (has `_go` suffix). The function `f` takes an explicit proof `h : i < as.length`, so V variant cannot eliminate it. |

### `Lemmas.lean`

| Lemma | Disposition | Notes |
|-------|-------------|-------|
| `get_eq_getElem` (line 196) | NOT APPLICABLE | Bridge lemma: `l.get i = l[i.1]'i.2`. Relates `get` (deprecated) to `getElem`. No V variant needed. |
| `getElem_eq_iff` (line 276) | NOT APPLICABLE | Iff lemma: `l[i] = x ↔ l[i]? = some x`. The proof `h` is needed for the forward direction. A V variant would be: `l｢i｣ = x ↔ ...` which is trivially true when `i` is out of bounds (both sides become garbage). Not useful for rewriting. |
| `getElem_of_eq` (line 320) | NOT APPLICABLE | Rewriting helper: `l[i] = l'[i]'(h ▸ w)` given `h : l = l'`. This is a proof transport lemma. A V variant would trivially follow from `congr`. |
| `getElem_zero` (line 329) | NOT APPLICABLE | Bridge: `l[0] = l.head (...)`. Relates `getElem` to `head`. The V analogue `getElemV_zero_eq_headV` already exists (line 1209). |
| `getElem_concat_length` (line 376) | FALSE POSITIVE | `getElemV_concat_length` already exists (line 372). |
| `eq_getElem_of_length_eq_one` (line 383) | NOT APPLICABLE | These reconstruct a list from its elements: `l = [l[0]'..., ...]`. A V variant would be meaningless since the proof is needed to establish `l.length = n`. |
| `eq_getElem_of_length_eq_two` (line 386) | NOT APPLICABLE | Same reasoning. |
| `eq_getElem_of_length_eq_three` (line 389) | NOT APPLICABLE | Same reasoning. |
| `eq_getElem_of_length_eq_four` (line 392) | NOT APPLICABLE | Same reasoning. |
| `getElem_set_self` (line 698) | FALSE POSITIVE | `getElemV_set_self` already exists (line 689). |
| `getElem_set_ne` (line 726) | FALSE POSITIVE | `getElemV_set_ne` already exists (line 715). |
| `getElem_set` (line 748) | FALSE POSITIVE | `getElemV_set` already exists (line 738). |
| `set_getElem_self` (line 780) | FALSE POSITIVE | `set_getElemV_self` already exists (line 772). |
| `getLast_eq_getElem` (line 899) | NOT APPLICABLE | Bridge: `getLast l h = l[l.length - 1]'(...)`. The V analogue `getLastV_eq_getElemV` already exists (line 1029). |
| `getElem_length_sub_one_eq_getLast` (line 908) | NOT APPLICABLE | Reverse bridge (same info as above). `getElemV_length_sub_one_eq_getLastV` already exists (line 1040). |
| `head_eq_getElem` (line 1109) | NOT APPLICABLE | Bridge: `head l h = l[0]'(...)`. The V analogue `headV_eq_getElemV` already exists (line 1195). |
| `getElem_zero_eq_head` (line 1114) | NOT APPLICABLE | Reverse bridge. `getElemV_zero_eq_headV` already exists (line 1209). |
| `getElem_tail` (line 1283) | FALSE POSITIVE | `getElemV_tail` already exists (line 1277). |
| `getElem_dropLast` (line 3570) | FALSE POSITIVE | `getElemV_dropLast` already exists (line 3560). |
| `getElem_replace` (line 3895) | FALSE POSITIVE | `getElemV_replace` already exists (line 3884). |
| `getElem_insert` (line 4071) | FALSE POSITIVE | `getElemV_insert` already exists (line 4062). |
| `getLast_mem` (line 933) | FALSE POSITIVE | `getLastV_mem` already exists (line 1068). |
| `head_mem` (line 1140) | ALREADY PLANNED | Step 1.3 plans to annotate `headV_mem` (already exists at line 1220). |

### `Nat/Pairwise.lean`

| Lemma | Disposition | Notes |
|-------|-------------|-------|
| `map_getElem_sublist` (line 30) | NOT APPLICABLE | Uses `Fin l.length` indices explicitly. The statement is about `is.map (l[·])` being a sublist. The `Fin` type carries its own proof; V variant not applicable. |
| `sublist_eq_map_getElem` (line 49) | NOT APPLICABLE | Existential: `∃ is : List (Fin l.length), l' = is.map (l[·]) ∧ ...`. Same `Fin`-based reasoning. |
| `pairwise_iff_getElem` (line 65) | NOT APPLICABLE | Quantified: `Pairwise R l ↔ ∀ (i j) (_hi : i < l.length) (_hj : j < l.length) (_hij : i < j), R l[i] l[j]`. The proofs `_hi`, `_hj` are needed to make `l[i]`, `l[j]` well-defined and to ensure the quantification is meaningful. A V variant would quantify over all `i, j` including out-of-bounds, making the iff false. |

### `Nat/Sublist.lean`

| Lemma | Disposition | Notes |
|-------|-------------|-------|
| `suffix_iff_getElem` (line 70) | NOT APPLICABLE | Quantified iff with explicit bounds: `∀ i (_ : i < l₁.length), l₂[i + ...] = l₁[i]`. Proofs are needed for correctness; a V variant would be vacuously true for out-of-bounds indices. |

### `Nat/TakeDrop.lean`

| Lemma | Disposition | Notes |
|-------|-------------|-------|
| `getElem_take` (line 59 of Nat/TakeDrop.lean) | NOT APPLICABLE | Rewrites `(xs.take j)[i]` to `xs[i]'(...)`. The LHS requires `i < (xs.take j).length` which is a stronger condition than `i < xs.length`. A V variant `(xs.take j)｢i｣ = xs｢i｣` would be true but only useful when `i < j`; otherwise the LHS is already garbage. However, this might be useful for `simp`. **Candidate — but see below.** Actually, the existing `getElem?_take` already handles the `?` case with an `if`. The V variant would collapse to the same: out-of-bounds returns default on both sides. This is already handled by `getElem?`/`getElemV` interaction. Skip. |
| `take_eq_append_getElem_of_pos` (line 192) | NOT APPLICABLE | Statement: `l.take i = l.take (i-1) ++ [l[i-1]]`. The proof `h₂ : i < l.length` is needed for `l[i-1]` to be valid. A V variant would produce garbage when out of bounds. |
| `getElem_drop` (line 237 of Nat/TakeDrop.lean) | NOT APPLICABLE | Rewrites `(xs.drop i)[j]` to `xs[i+j]'(...)`. Both sides need proofs for correctness; V variant would be trivially true out-of-bounds. The `getElem?_drop` already provides the proof-free version. |
| `mem_take_iff_getElem` (line 263) | NOT APPLICABLE | Quantified iff: `a ∈ l.take i ↔ ∃ (j) (hm : j < min i l.length), l[j] = a`. The bound `hm` is essential to the characterization. |
| `mem_drop_iff_getElem` (line 273) | NOT APPLICABLE | Same pattern as above. |
| `getElem_zipWith` (line 600) | NOT APPLICABLE | Statement: `(zipWith f l l')[i] = f (l[i]'...) (l'[i]'...)`. Three different proof-taking `getElem` calls on different lists. A V variant would need `Nonempty γ` and would return garbage when `i` is out of bounds for any of the three lists. The `getElem?_zipWith` already handles the proof-free case. |
| `getElem_zip` (line 650) | **CANDIDATE** | See confirmed gaps below. Needs `{_ : Nonempty (α × β)}` and bound proof `h : i < (zip l l').length` because `Classical.ofNonempty (α × β)` may differ from `(Classical.ofNonempty α, Classical.ofNonempty β)`. |

### `Nat/Erase.lean`

| Lemma | Disposition | Notes |
|-------|-------------|-------|
| `getElem_eraseIdx` (line 59) | **CANDIDATE** | See below. |
| `getElem_eraseIdx_of_lt` (line 68) | **CANDIDATE** | See below. |
| `getElem_eraseIdx_of_ge` (line 75) | **CANDIDATE** | See below. |

### `Nat/InsertIdx.lean`

| Lemma | Disposition | Notes |
|-------|-------------|-------|
| `getElem_insertIdx_of_lt` (line 146) | **CANDIDATE** | See below. |
| `getElem_insertIdx_self` (line 161) | **CANDIDATE** | See below. |
| `getElem_insertIdx_of_gt` (line 175) | **CANDIDATE** | See below. |
| `getElem_insertIdx` (line 203) | **CANDIDATE** | See below. |

### `Nat/Basic.lean`

| Lemma | Disposition | Notes |
|-------|-------------|-------|
| `getElem_eq_getElem_reverse` (line 95) | NOT APPLICABLE | Bridge: `l[i] = l.reverse[l.length - 1 - i]'(...)`. The V analogue `getElemV_reverse` already exists (line 2800 of Lemmas.lean). |
| `getElem_intersperse` (line 184) | **CANDIDATE** | See below. |
| `getElem_eq_getElem_intersperse_two_mul` (line 195) | NOT APPLICABLE | Bridge (reverse direction of `getElemV_intersperse_two_mul` which already exists). |
| `mem_eraseIdx_iff_getElem` (line 203) | NOT APPLICABLE | Quantified iff: `x ∈ eraseIdx l k ↔ ∃ i h, i ≠ k ∧ l[i]'h = x`. The proof `h` is essential to the characterization. |

### `Nat/Modify.lean`

| Lemma | Disposition | Notes |
|-------|-------------|-------|
| `getElem_modifyHead` (line 43) | ALREADY PLANNED | Step 1.4 covers `getElemV_modifyHead_zero` and `getElemV_modifyHead_succ` (which already exist). The combined `getElem_modifyHead` doesn't need a separate V variant since the split versions cover it. |

### `TakeDrop.lean`

| Lemma | Disposition | Notes |
|-------|-------------|-------|
| `drop_eq_getElem_cons` (line 82) | NOT APPLICABLE | Statement: `drop i l = l[i] :: drop (i+1) l`. This constructs a list value; the proof `h : i < l.length` is needed for the cons to be valid. A V variant would produce garbage when out-of-bounds. |
| `take_append_getElem` (line 209) | NOT APPLICABLE | Statement: `(l.take i) ++ [l[i]] = l.take (i+1)`. Same reasoning — proof needed for list construction. |

### `Sublist.lean`

| Lemma | Disposition | Notes |
|-------|-------------|-------|
| `prefix_iff_getElem` (line 990) | NOT APPLICABLE | Quantified iff: `l₁ <+: l₂ ↔ ∃ (h : l₁.length ≤ l₂.length), ∀ i (hx : i < l₁.length), l₁[i] = l₂[i]'(...)`. Proofs are essential for the characterization. |

### `OfFn.lean`

| Lemma | Disposition | Notes |
|-------|-------------|-------|
| `ofFn_getElem` (line 115) | NOT APPLICABLE | Statement: `List.ofFn (fun i : Fin xs.length => xs[i.val]) = xs`. Uses `Fin`-based indexing. Not a V-variant candidate (it's about `ofFn`, not about accessing elements). |

### `Range.lean`

| Lemma | Disposition | Notes |
|-------|-------------|-------|
| `getElem_zipIdx` (line 233) | NOT APPLICABLE | Result type is `α × Nat` (a pair). A V variant would need `Nonempty (α × Nat)` and would produce a garbage pair when out of bounds. The existing `getElem?_zipIdx` handles the proof-free case. |

### `Scan/Lemmas.lean`

| Lemma | Disposition | Notes |
|-------|-------------|-------|
| `getElem_scanl_zero` (line 174) | ALREADY PLANNED | Step 1.7 plans `getElemV_scanl` (combined, already exists). This is a special case. Also, `headV_scanl` already exists. |
| `getElem_succ_scanl` (line 220) | ALREADY PLANNED | Step 1.7 plans `getElemV_scanl` (combined, already exists at line 149). |
| `getElem_scanr_zero` (line 348) | ALREADY PLANNED | Step 1.7 plans `getElemV_scanr` (combined, already exists at line 331). Also, `head_scanr`/`head?_scanr` cover the zero case. |

---

## Confirmed gaps: Lemmas needing V variants

### `Attach.lean` — pmap/attachWith/attach (3 create)

These lemmas retain a proof parameter (`hn : i < l.length`) which is needed to construct
the `Nonempty` witness and the proof arguments to `f` / `H` on the RHS. The V variant
replaces `[i]'proof` with `｢i｣` on both LHS and RHS.

Per SIGNATURE_SPEC.md, use `hn : i < l.length` (simp normal form) rather than
`hn : i < (pmap f l h).length`.

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getElemV_pmap` | `getElem_pmap` (line 250) | `@[simp, grind =]` | create |
| `getElemV_attachWith` | `getElem_attachWith` (line 275) | `@[simp, grind =]` | create |
| `getElemV_attach` | `getElem_attach` (line 281) | `@[simp, grind =]` | create |

#### Suggested signatures

```lean
@[simp, grind =]
theorem getElemV_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (h : ∀ a ∈ l, p a)
    {i : Nat} (hn : i < l.length) :
    haveI : Nonempty β := ⟨f (l[i]'hn) (h _ (getElem_mem hn))⟩
    (pmap f l h)｢i｣ = f l｢i｣ (h _ (getElem_mem hn))

@[simp, grind =]
theorem getElemV_attachWith {xs : List α} {P : α → Prop} {H : ∀ a ∈ xs, P a}
    {i : Nat} (h : i < xs.length) :
    haveI : Nonempty { x // P x } := ⟨⟨xs[i]'h, H _ (getElem_mem h)⟩⟩
    (xs.attachWith P H)｢i｣ = ⟨xs｢i｣, H _ (getElem_mem h)⟩

@[simp, grind =]
theorem getElemV_attach {xs : List α} {i : Nat} (h : i < xs.length) :
    haveI : Nonempty { x // x ∈ xs } := ⟨⟨xs[i]'h, getElem_mem h⟩⟩
    xs.attach｢i｣ = ⟨xs｢i｣, getElem_mem h⟩
```

### `Nat/Erase.lean` — `getElemV_eraseIdx` family (3 create)

These lemmas rewrite `(l.eraseIdx i)[j]` in terms of `l[j]` or `l[j+1]`. A V variant
is meaningful because the RHS indexes into the original list `l`, and the relationship
between `j` and the erased index `i` determines which element is returned.

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getElemV_eraseIdx` | `getElem_eraseIdx` (line 59) | `@[grind =]` | create |
| `getElemV_eraseIdx_of_lt` | `getElem_eraseIdx_of_lt` (line 68) | none | create |
| `getElemV_eraseIdx_of_ge` | `getElem_eraseIdx_of_ge` (line 75) | none | create |

#### Suggested signatures

```lean
@[grind =] theorem getElemV_eraseIdx {_ : Nonempty α} {l : List α} {i j : Nat} :
    (l.eraseIdx i)｢j｣ = if j < i then l｢j｣ else l｢j + 1｣

theorem getElemV_eraseIdx_of_lt {_ : Nonempty α} {l : List α} {i j : Nat} (h' : j < i) :
    (l.eraseIdx i)｢j｣ = l｢j｣

theorem getElemV_eraseIdx_of_ge {_ : Nonempty α} {l : List α} {i j : Nat} (h' : i ≤ j) :
    (l.eraseIdx i)｢j｣ = l｢j + 1｣
```

Note: The `_of_lt` and `_of_ge` variants keep the explicit bound conditions (`h'`) since
these are needed for the equation to be correct (not just for well-typedness). The combined
`getElemV_eraseIdx` uses an `if` to cover both cases without a proof, since `getElemV`
returns garbage for out-of-bounds access on both sides consistently.

### `Nat/InsertIdx.lean` — `getElemV_insertIdx` family (3 create)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getElemV_insertIdx` | `getElem_insertIdx` (line 203) | `@[grind =]` | create |
| `getElemV_insertIdx_of_lt` | `getElem_insertIdx_of_lt` (line 146) | none | create |
| `getElemV_insertIdx_self` | `getElem_insertIdx_self` (line 161) | `@[simp]` | create |
| `getElemV_insertIdx_of_gt` | `getElem_insertIdx_of_gt` (line 175) | none | create |

#### Suggested signatures

```lean
@[grind =] theorem getElemV_insertIdx {l : List α} {a : α} {i j : Nat}
    (h : j < l.length + 1) :
    haveI : Nonempty α := ⟨a⟩
    (l.insertIdx i a)｢j｣ = if j < i then l｢j｣ else if j = i then a else l｢j - 1｣

theorem getElemV_insertIdx_of_lt {l : List α} {a : α} {i j : Nat} (h : j < i) :
    haveI : Nonempty α := ⟨a⟩
    (l.insertIdx i a)｢j｣ = l｢j｣

@[simp] theorem getElemV_insertIdx_self {l : List α} {a : α} {i : Nat} (w : i ≤ l.length) :
    haveI : Nonempty α := ⟨a⟩
    (l.insertIdx i a)｢i｣ = a

theorem getElemV_insertIdx_of_gt {l : List α} {a : α} {i j : Nat} (h : i < j) :
    haveI : Nonempty α := ⟨a⟩
    (l.insertIdx i a)｢j｣ = l｢j - 1｣
```

Note: `Nonempty α` is obtained from `⟨a⟩` (the element being inserted) rather than as an
instance parameter, following the pattern of `getElemV_insert` in Lemmas.lean.

### `Nat/Basic.lean` — `getElemV_intersperse` (1 create)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getElemV_intersperse` | `getElem_intersperse` (line 184) | `@[grind =]` | create |

Note: `getElemV_intersperse_two_mul` and `getElemV_intersperse_two_mul_add_one` already exist
(ALREADY PLANNED in Step 1.5). This is the combined version.

#### Suggested signature

```lean
@[grind =] theorem getElemV_intersperse {l : List α} {sep : α} {i : Nat}
    (h : i < (l.intersperse sep).length) :
    haveI : Nonempty α := ⟨sep⟩
    (l.intersperse sep)｢i｣ = if i % 2 = 0 then l｢i / 2｣ else sep
```

Note: The proof `h : i < (l.intersperse sep).length` is kept because the `else` branch
returns `sep` (a specific value), not garbage. Without this condition, out-of-bounds access
on the LHS returns garbage but the RHS could return `sep`, making the equation false.
This follows the same pattern as `getElem_intersperse`.

### `Nat/TakeDrop.lean` — `getElemV_zip` (1 create)

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getElemV_zip` | `getElem_zip` (line 650) | `@[simp, grind =]` | create |

#### Suggested signature

```lean
@[simp, grind =] theorem getElemV_zip {_ : Nonempty (α × β)} {l : List α} {l' : List β}
    {i : Nat} (h : i < (zip l l').length) :
    (zip l l')｢i｣ = (l｢i｣, l'｢i｣)
```

Note: The bound proof `h : i < (zip l l').length` is kept because
`Classical.ofNonempty (α × β)` may differ from `(Classical.ofNonempty α, Classical.ofNonempty β)`.
Use `Nonempty (α × β)` (not separate instances) for the same reason.

---

## Summary

| File | Creates | Notes |
|------|---------|-------|
| Attach.lean | 3 | `getElemV_pmap`, `getElemV_attachWith`, `getElemV_attach` |
| Nat/Erase.lean | 3 | `getElemV_eraseIdx`, `_of_lt`, `_of_ge` |
| Nat/InsertIdx.lean | 4 | `getElemV_insertIdx`, `_of_lt`, `_self`, `_of_gt` |
| Nat/Basic.lean | 1 | `getElemV_intersperse` |
| Nat/TakeDrop.lean | 1 | `getElemV_zip` |
| **Total** | **12** | |

All other candidates (52 of 63 original entries) are either false positives (V variant exists),
already planned in Step 1, or not applicable for V variant treatment.
