# Step 3a.2: Array V Lemma Parity (Remaining)

Status: good; Refinement Needed: no

## Files

Multiple files under `src/Init/Data/Array/`.

## Summary

After auditing all candidates from the stub against existing V variants, Step 1.1 coverage,
and semantic applicability, the following lemmas are confirmed as actionable gaps.

## FALSE POSITIVES (V variant already exists)

| Candidate | File | Reason |
|-----------|------|--------|
| `getElem_toList` | `Basic.lean:93` | `getElemV_toList` exists at line 99 |
| `getElem_toArray` | `Basic.lean:140` | `getElemV_toArray` exists at line 150 |
| `getElem_push_eq` | `Lemmas.lean:183` | `getElemV_push_eq` exists at line 187 |
| `getElem_push` | `Lemmas.lean:191` | `getElemV_push` exists at line 198 |

## ALREADY PLANNED in Step 1.1

All the following were planned and implemented in Step 1.1:
`getElemV_push_eq`, `getElemV_push`, `getElemV_set_self`, `getElemV_set_ne`, `getElemV_set`,
`set_getElemV_self`, `getElemV_setIfInBounds`, `getElemV_setIfInBounds_self`,
`getElemV_setIfInBounds_ne`, `getElemV_filter`, `getElemV_append`, `getElemV_append_left`,
`getElemV_append_right`, `getElemV_modify`, `getElemV_swap`, `getElemV_swap_right`,
`getElemV_swap_left`, `getElemV_swap_of_ne`, `getElemV_swapIfInBounds`, `getElemV_replace`,
`getElemV_ofFn`.

## NOT APPLICABLE (V variant not meaningful)

| Candidate | File | Reason |
|-----------|------|--------|
| `getElem_pmap` | `Attach.lean:260` | **MOVED TO ACTIONABLE** — V variant retains `hn : i < xs.size` (simp normal form) but replaces `[i]'proof` with `｢i｣`. See actionable gaps. |
| `getElem_attachWith` | `Attach.lean:278` | **MOVED TO ACTIONABLE** — same pattern. |
| `getElem_attach` | `Attach.lean:284` | **MOVED TO ACTIONABLE** — same pattern. |
| `boole_getElem_le_countP` | `Count.lean:121` | `getElem` appears as sub-expression `xs[i]` inside `if p xs[i] then 1 else 0`. The statement is only true when `i < xs.size` (otherwise `xs｢i｣` returns garbage and the inequality may not hold). Dropping the proof makes the statement false. |
| `boole_getElem_le_count` | `Count.lean:237` | Same reasoning as `boole_getElem_le_countP`. |
| `eraseP_of_forall_getElem_not` | `Erase.lean:41` | Uses `∀ i, (h : i < xs.size) → ¬p xs[i]`. The bound proof `h` is essential for the universal quantifier to be meaningful; dropping it would require `¬p xs｢i｣` for all `i` including out-of-bounds, which is not equivalent. |
| `mem_eraseIdx_iff_getElem` | `Erase.lean:418` | Uses `∃ i w, i ≠ k ∧ xs[i]'w = x`. The existential needs the bound proof `w` to state `xs[i]'w = x`; a V variant `xs｢i｣ = x` would be a weaker statement (true for garbage values). Not meaningful. |
| `push_extract_getElem` | `Extract.lean:173` | `as[j]` is used as a value pushed onto the array; the bound proof `h : j < as.size` is a hypothesis of the theorem (needed to make both sides well-formed). V variant would need the same `j < as.size` proof, gaining nothing. |
| `mem_extract_iff_getElem` | `Extract.lean:328` | Uses `∃ (k : Nat) (hm : k < ...), as[i + k] = a`. The existential bound is essential; V variant not meaningful. |
| `getElem_zero_flatten` | `Find.lean:128,139` | The `.proof` helper at line 128 is internal. The theorem at line 139 has `(h : 0 < xss.flatten.size)` — the result type involves `Option.get` on `findSome?` and the proof `h` is essential for the statement. A V variant would need `Nonempty α` but also the same `h` to make `Option.get` work. Not meaningful. |
| `findIdx_getElem` | `Find.lean:370` | States `p xs[xs.findIdx p]` with `w : xs.findIdx p < xs.size`. The bound is essential for the statement to be true (out-of-bounds `xs｢xs.findIdx p｣` is garbage). |
| `lt_of_getElem` | `Lemmas.lean:4607` | Trivial lemma: extracts `i < xs.size` from implicit proof. No getElem in the conclusion to replace with V. |
| `getElem_fin_eq_getElem_toList` | `Lemmas.lean:4611` | States `xs[i] = xs.toList[i]` for `i : Fin xs.size`. Both sides use bounded getElem; `Fin` already carries the proof. A V variant `xs｢i｣ = xs.toList｢i｣` would be subsumed by `getElemV_toList`. |
| `getElem_mem_toList` | `Lemmas.lean:4620` | States `xs[i] ∈ xs.toList` with `h : i < xs.size`. V variant would need `h` to make the statement true (out-of-bounds garbage is not necessarily in `toList`). |
| `ofFn_getElem` | `OfFn.lean:62` | States `ofFn (fun i : Fin xs.size => xs[i]) = xs`. The `Fin` bound is intrinsic; not an indexing lemma. |
| `getElem_eq_iff` | `Lemmas.lean:158` | States `xs[i] = x ↔ xs[i]? = some x` with `h : i < xs.size`. V variant: `xs｢i｣ = x` without bound proof is NOT equivalent to `xs[i]? = some x` (out-of-bounds garbage could equal `x`). |

## NOT APPLICABLE (proof still required, no benefit)

| Candidate | File | Reason |
|-----------|------|--------|
| `getElem_eraseIdx_of_lt` | `Erase.lean:432` | Specialized case of `getElem_eraseIdx` for `j < i`. Requires `w : i < xs.size` and `h : j < (xs.eraseIdx i).size` — both needed for the statement. V variant would still need these proofs. |
| `getElem_eraseIdx_of_ge` | `Erase.lean:437` | Same reasoning — requires `w : i < xs.size`, `h : j < ...`, `h' : i ≤ j`. V variant needs same proofs. |
| `getElem_swapIfInBounds_of_size_le_left` | `Lemmas.lean:4265` | Requires `hi : xs.size ≤ i` and `hk : k < ...`. The proofs are about the arguments, not the getElem index. V variant would still require the same hypotheses. |
| `getElem_swapIfInBounds_of_size_le_right` | `Lemmas.lean:4274` | Same reasoning. |

## Excluded (internal/deprecated) — confirmed

| Candidate | File | Reason |
|-----------|------|--------|
| `getElem_extract_loop_*` | `Lemmas.lean` | Internal helpers (loop suffix). |
| `getElem_extract_aux` | `Lemmas.lean` | Internal helper (aux suffix). |
| `getElem_swap` | `Lemmas.lean:4196` | Deprecated. |

## ACTIONABLE GAPS — V variants to create

### `Attach.lean` (3 create)

These retain a proof parameter (`hn : i < xs.size`, simp normal form) needed to construct
the `Nonempty` witness and the proof arguments to `f` / `H` on the RHS.

| # | V lemma | Counterpart | Annotation | Suggested signature |
|---|---------|-------------|------------|---------------------|
| A1 | `getElemV_pmap` | `getElem_pmap` | `@[simp, grind =]` | `theorem getElemV_pmap {p : α → Prop} (f : ∀ a, p a → β) {xs : Array α} (h : ∀ a ∈ xs, p a) {i : Nat} (hn : i < xs.size) : haveI : Nonempty β := ⟨f (xs[i]'hn) (h _ (getElem_mem hn))⟩; (pmap f xs h)｢i｣ = f xs｢i｣ (h _ (getElem_mem hn))` |
| A2 | `getElemV_attachWith` | `getElem_attachWith` | `@[simp, grind =]` | `theorem getElemV_attachWith {xs : Array α} {P : α → Prop} {H : ∀ a ∈ xs, P a} {i : Nat} (h : i < xs.size) : haveI : Nonempty { x // P x } := ⟨⟨xs[i]'h, H _ (getElem_mem h)⟩⟩; (xs.attachWith P H)｢i｣ = ⟨xs｢i｣, H _ (getElem_mem h)⟩` |
| A3 | `getElemV_attach` | `getElem_attach` | `@[simp, grind =]` | `theorem getElemV_attach {xs : Array α} {i : Nat} (h : i < xs.size) : haveI : Nonempty { x // x ∈ xs } := ⟨⟨xs[i]'h, getElem_mem h⟩⟩; xs.attach｢i｣ = ⟨xs｢i｣, getElem_mem h⟩` |

### `Lemmas.lean`

| # | V lemma | Counterpart | Annotation | Suggested signature |
|---|---------|-------------|------------|---------------------|
| 1 | `getElemV_push_lt` | `getElem_push_lt` | none | `theorem getElemV_push_lt {xs : Array α} {x : α} {i : Nat} (h : i < xs.size) : haveI : Nonempty α := ⟨x⟩; (xs.push x)｢i｣ = xs｢i｣` |
| 2 | `getElemV_singleton` | `getElem_singleton` | none | `theorem getElemV_singleton {a : α} {i : Nat} (h : i < 1) : haveI : Nonempty α := ⟨a⟩; #[a]｢i｣ = a` |
| 3 | `getElemV_eq_getElemV_reverse` | `getElem_eq_getElem_reverse` | none | `theorem getElemV_eq_getElemV_reverse {_ : Nonempty α} {xs : Array α} {i : Nat} (h : i < xs.size) : xs｢i｣ = xs.reverse｢xs.size - 1 - i｣` |
| 4 | `getElemV_shrink` | `getElem_shrink` | none | `theorem getElemV_shrink {_ : Nonempty α} {xs : Array α} {i j : Nat} (h : j < (xs.shrink i).size) : (xs.shrink i)｢j｣ = xs｢j｣` |
| 5 | `getElemV_modify_self` | `getElem_modify_self` | none | `theorem getElemV_modify_self {xs : Array α} {i : Nat} (f : α → α) (h : i < xs.size) : haveI : Nonempty α := ⟨f xs[i]⟩; (xs.modify i f)｢i｣ = f xs｢i｣` |
| 6 | `getElemV_modify_of_ne` | `getElem_modify_of_ne` | none | `theorem getElemV_modify_of_ne {_ : Nonempty α} {xs : Array α} {i : Nat} (h : i ≠ j) (f : α → α) : (xs.modify i f)｢j｣ = xs｢j｣` |
| 7 | `getElemV_swapIfInBounds_left` | `getElem_swapIfInBounds_left` | `@[simp]` | `theorem getElemV_swapIfInBounds_left {xs : Array α} {i j : Nat} (hj : j < xs.size) : haveI : Nonempty α := ⟨xs[j]⟩; (xs.swapIfInBounds i j)｢i｣ = xs｢j｣` |
| 8 | `getElemV_swapIfInBounds_right` | `getElem_swapIfInBounds_right` | `@[simp]` | `theorem getElemV_swapIfInBounds_right {xs : Array α} {i j : Nat} (hi : i < xs.size) : haveI : Nonempty α := ⟨xs[i]⟩; (xs.swapIfInBounds i j)｢j｣ = xs｢i｣` |
| 9 | `getElemV_swapIfInBounds_of_ne_of_ne` | `getElem_swapIfInBounds_of_ne_of_ne` | `@[simp]` | `theorem getElemV_swapIfInBounds_of_ne_of_ne {_ : Nonempty α} {xs : Array α} {i j k : Nat} (hi : k ≠ i) (hj : k ≠ j) : (xs.swapIfInBounds i j)｢k｣ = xs｢k｣` |
| 10 | `getElemV_range` | `getElem_range` | `@[simp, grind =]` | `theorem getElemV_range {n : Nat} {i : Nat} (h : i < n) : (Array.range n)｢i｣ = i` |

### `Erase.lean`

| # | V lemma | Counterpart | Annotation | Suggested signature |
|---|---------|-------------|------------|---------------------|
| 11 | `getElemV_eraseIdx` | `getElem_eraseIdx` | `@[grind =]` | `theorem getElemV_eraseIdx {_ : Nonempty α} {xs : Array α} {i : Nat} (h : i < xs.size) {j : Nat} : (xs.eraseIdx i)｢j｣ = if j < i then xs｢j｣ else xs｢j + 1｣` |

### `InsertIdx.lean`

| # | V lemma | Counterpart | Annotation | Suggested signature |
|---|---------|-------------|------------|---------------------|
| 12 | `getElemV_insertIdx` | `getElem_insertIdx` | `@[grind =]` | `theorem getElemV_insertIdx {xs : Array α} {x : α} {i k : Nat} (w : i ≤ xs.size) (h : k < xs.size + 1) : haveI : Nonempty α := ⟨x⟩; (xs.insertIdx i x)｢k｣ = if k < i then xs｢k｣ else if k = i then x else xs｢k - 1｣` |
| 13 | `getElemV_insertIdx_of_lt` | `getElem_insertIdx_of_lt` | none | `theorem getElemV_insertIdx_of_lt {xs : Array α} {x : α} {i k : Nat} (w : i ≤ xs.size) (h : k < i) : haveI : Nonempty α := ⟨x⟩; (xs.insertIdx i x)｢k｣ = xs｢k｣` |
| 14 | `getElemV_insertIdx_self` | `getElem_insertIdx_self` | none | `theorem getElemV_insertIdx_self {xs : Array α} {x : α} {i : Nat} (w : i ≤ xs.size) : haveI : Nonempty α := ⟨x⟩; (xs.insertIdx i x)｢i｣ = x` |
| 15 | `getElemV_insertIdx_of_gt` | `getElem_insertIdx_of_gt` | none | `theorem getElemV_insertIdx_of_gt {xs : Array α} {x : α} {i k : Nat} (w : k ≤ xs.size) (h : k > i) : haveI : Nonempty α := ⟨x⟩; (xs.insertIdx i x)｢k｣ = xs｢k - 1｣` |

### `Zip.lean`

| # | V lemma | Counterpart | Annotation | Suggested signature |
|---|---------|-------------|------------|---------------------|
| 16 | `getElemV_zip` | `getElem_zip` | `@[simp, grind =]` | `theorem getElemV_zip {_ : Nonempty (α × β)} {as : Array α} {bs : Array β} {i : Nat} (h : i < (zip as bs).size) : (zip as bs)｢i｣ = (as｢i｣, bs｢i｣)` |

### `Mem.lean`

| # | V lemma | Counterpart | Annotation | Suggested signature | Notes |
|---|---------|-------------|------------|---------------------|-------|
| 17 | `sizeOf_getElemV` | `sizeOf_getElem` | `@[simp]` | `theorem sizeOf_getElemV [SizeOf α] (as : Array α) (i : Nat) (h : i < as.size) : haveI : Nonempty α := ⟨as[i]⟩; sizeOf as｢i｣ < sizeOf as` | Used by `decreasing_trivial` — requires `h : i < as.size` since the bound is only true for in-bounds elements. The `haveI` avoids requiring `Nonempty α` as a hypothesis. Also register with `array_get_dec` tactic macro. |

## Notes

- `getElemV_push_lt` keeps `h : i < xs.size` because it is needed for the statement to be true
  (without it, `(xs.push x)｢i｣` could be `x` when `i = xs.size`). However, unlike the
  proof-taking counterpart, the V variant does not need `i < (xs.push x).size` (which is
  what `getElem_push_lt` uses via the `have` clause).
- `getElemV_singleton` keeps `h : i < 1` because without it, `#[a]｢i｣` returns garbage for `i ≥ 1`.
- `getElemV_eq_getElemV_reverse` keeps `h : i < xs.size` because `xs.size - 1 - i` would
  underflow and `reverse｢...｣` would return garbage otherwise.
- `getElemV_shrink` keeps `h : j < (xs.shrink i).size` because the equality is only true
  in-bounds. However, this lemma is somewhat redundant since `shrink_eq_take` simplifies
  `shrink` to `take`. Include for completeness.
- `getElemV_modify_self` keeps `h : i < xs.size` because `modify` is a no-op when out-of-bounds.
- `getElemV_eraseIdx` keeps `h : i < xs.size` because `eraseIdx` requires it. The V variant
  drops the output-side proof `j < (xs.eraseIdx i).size`.
- `getElemV_insertIdx` keeps `w : i ≤ xs.size` because `insertIdx` requires it. It also keeps
  `h : k < xs.size + 1` because the `= i` case would be problematic otherwise — when `k = xs.size + 1`
  (out of bounds), the LHS is garbage but the RHS would be `xs｢k - 1｣` which is also garbage
  but potentially a different `Classical.ofNonempty`.
- `getElemV_zip`: Use `{_ : Nonempty (α × β)}` (not separate `Nonempty α` + `Nonempty β`)
  because `Classical.ofNonempty (α × β)` may differ from `(Classical.ofNonempty α, Classical.ofNonempty β)`.
  The bound proof `h : i < (zip as bs).size` is needed because out-of-bounds the LHS returns
  `Classical.ofNonempty (α × β)` but the RHS returns `(Classical.ofNonempty α, Classical.ofNonempty β)`,
  which may differ. This matches the List and Vector conventions.
- `sizeOf_getElemV` is special: it's used by `decreasing_trivial` through the `array_get_dec`
  tactic. The proof `h : i < as.size` cannot be dropped because `sizeOf (Classical.ofNonempty)`
  has no useful bound. The V variant should be added alongside the existing `sizeOf_getElem` and
  potentially registered in `array_get_dec`.
- `getElemV_range` keeps `h : i < n` because `(Array.range n)｢i｣` returns garbage (specifically
  `Classical.ofNonempty : Nat`, not `i`) when `i ≥ n`. Note: `Nonempty Nat` is available
  automatically, so no `haveI` is needed.
- `getElemV_swapIfInBounds_left/right` keep their respective bound proofs (`hj`/`hi`) because
  `swapIfInBounds` is a no-op when the index is out of bounds.

## Implementation order

1. `Attach.lean`: 3 lemmas (items A1–A3)
2. `Mem.lean`: `sizeOf_getElemV` (special, affects `decreasing_trivial`)
3. `Lemmas.lean`: 10 lemmas (items 1–10)
4. `Erase.lean`: `getElemV_eraseIdx` (item 11)
5. `InsertIdx.lean`: 4 lemmas (items 12–15)
6. `Zip.lean`: `getElemV_zip` (item 16)

Total: 20 new V variant lemmas.
