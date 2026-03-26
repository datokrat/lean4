# Step 3e.1: Array V Lemma Parity (Full Audit)

Status: not started; Refinement Needed: no

## Files

Multiple files under `src/Init/Data/Array/`.

## Goal

Add V variants for ALL remaining proof-taking lemmas in Array, including existential/quantified
statements, product-type indexing, and lemmas where proofs are still required for truth.

## ALREADY EXISTS — V variants that exist in the source

The following were listed as gaps but already exist:

| # | V lemma | Location |
|---|---------|----------|
| 4 | `backV_pop` | `Lemmas.lean:256` |
| 9 | `getElemV_append` | `Lemmas.lean:1908` |
| 10 | `getElemV_append_left` | `Lemmas.lean:1920` |
| 11 | `getElemV_append_right` | `Lemmas.lean:1931` |
| 13 | `getElemV_eq_getElemV_reverse` | `Lemmas.lean:2716` |
| 14 | `backV_append` | `Lemmas.lean:3715` |
| 15 | `getElemV_modify` | `Lemmas.lean:4130` |
| 16 | `getElemV_swap` | `Lemmas.lean:4182` |
| 17 | `getElemV_swap_of_ne` | `Lemmas.lean:4219` |
| 18 | `getElemV_swapIfInBounds` | `Lemmas.lean:4273` |
| 22 | `getElemV_eq_getD` | `Lemmas.lean:4645` |

## ACTIONABLE GAPS — V variants to create

### `Lemmas.lean` (~11 lemmas)

| # | V lemma | Counterpart | Annotation |
|---|---------|-------------|------------|
| 1 | `getElemV_eq_iff` | `getElem_eq_iff` (line 158) | none |
| 2 | `getElemV_eq_getElem` | `getElem_eq_getElem?_get` (line 162) | none |
| 3 | `getD_getElemV` | `getD_getElem?` (line 166) | none |
| 5 | `getElemV_of_mem` | `getElem_of_mem` (line 509) | none |
| 6 | `mem_of_getElemV` | `mem_of_getElem` (line 516) | none |
| 7 | `mem_iff_getElemV` | `mem_iff_getElem` (line 523) | none |
| 8 | V-form of `any_eq` | `any_eq` (line 785) | `@[grind =]` |
| 12 | `getElemV_of_append` | `getElem_of_append` (line 1964) | none |
| 19 | `getElemV_swapIfInBounds_of_size_le_left` | line 4293 | `@[simp]` |
| 20 | `getElemV_swapIfInBounds_of_size_le_right` | line 4302 | `@[simp]` |
| 21 | `getElemV_replace_of_ne` | `getElem_replace_of_ne` (line 4405) | none |

Suggested signatures:

```lean
-- #1: getElem_eq_iff states: xs[i] = x ↔ xs[i]? = some x (with h : i < xs.size)
-- V variant: xs｢i｣ = x without bound proof is NOT equivalent to xs[i]? = some x
-- (out-of-bounds garbage could equal x). Keep bound proof for truth.
theorem getElemV_eq_iff {xs : Array α} {i : Nat} (h : i < xs.size) {_ : Nonempty α} :
    xs｢i｣ = x ↔ xs[i]? = some x

-- #2: getElem_eq_getElem?_get states: xs[i] = xs[i]?.get (by simp [h])
-- V variant replaces xs[i] with xs｢i｣; keeps h for the Option.get on the RHS.
theorem getElemV_eq_getElem {xs : Array α} {i : Nat} (h : i < xs.size) {_ : Nonempty α} :
    xs｢i｣ = xs[i]?.get (by simp [h])

-- #3: getD_getElem? states: xs[i]?.getD d = if p : i < xs.size then xs[i]'p else d
-- V variant: uses xs｢i｣ on the RHS of the if-then branch.
theorem getD_getElemV {_ : Nonempty α} {xs : Array α} {i : Nat} {d : α} :
    xs[i]?.getD d = if i < xs.size then xs｢i｣ else d

-- #5: getElem_of_mem states: ∃ (i : Nat) (h : i < xs.size), xs[i]'h = a
-- V variant drops the bound proof from the existential.
theorem getElemV_of_mem {a : α} {xs : Array α} (h : a ∈ xs) :
    ∃ i, xs｢i｣ = a

-- #6: mem_of_getElem states: xs[i] = a → a ∈ xs (with h : i < xs.size)
-- V variant keeps h because out-of-bounds garbage is not necessarily in xs.
theorem mem_of_getElemV {xs : Array α} {i : Nat} (h : i < xs.size) {a : α}
    (e : xs｢i｣ = a) : a ∈ xs

-- #7: mem_iff_getElem states: a ∈ xs ↔ ∃ (i : Nat) (h : i < xs.size), xs[i]'h = a
-- V variant drops bound proof from existential.
theorem mem_iff_getElemV {a : α} {xs : Array α} :
    a ∈ xs ↔ ∃ i, xs｢i｣ = a

-- #8: any_eq states: xs.any p = decide (∃ i : Nat, ∃ h, p (xs[i]'h))
-- V variant replaces ∃ i, ∃ h, p (xs[i]'h) with ∃ i, p xs｢i｣.
-- NOTE: This is NOT correct without a Nonempty bound — if α is empty then
-- xs is empty and both sides are false, but ∃ i, p xs｢i｣ with garbage could be true.
-- Keep {_ : Nonempty α} and the statement is only correct when quantifier is bounded.
-- Actually for empty xs, any p = false and ∃ i, p xs｢i｣ quantifies over all Nat.
-- This V variant is FALSE in general (p (Classical.ofNonempty) could be true when xs is empty).
-- SKIP or require i < xs.size.
@[grind =]
theorem anyV_eq {_ : Nonempty α} {xs : Array α} {p : α → Bool} :
    xs.any p = decide (∃ i, i < xs.size ∧ p xs｢i｣)

-- #12: getElem_of_append states:
--   xs[i]'(...) = a  given eq : xs = ys.push a ++ zs, h : ys.size = i
-- V variant: uses xs｢i｣ on the LHS. Keeps eq and h (needed for truth).
theorem getElemV_of_append {xs ys zs : Array α} {a : α} (eq : xs = ys.push a ++ zs)
    (h : ys.size = i) :
    haveI : Nonempty α := ⟨a⟩; xs｢i｣ = a

-- #19: getElem_swapIfInBounds_of_size_le_left states:
--   (xs.swapIfInBounds i j)[k] = xs[k] given hi : xs.size ≤ i, hk : k < ...
-- V variant: uses ｢k｣ on both sides. Keeps hi (needed for truth: swap is no-op).
@[simp]
theorem getElemV_swapIfInBounds_of_size_le_left {_ : Nonempty α} {xs : Array α} {i j k : Nat}
    (hi : xs.size ≤ i) :
    (xs.swapIfInBounds i j)｢k｣ = xs｢k｣

-- #20: getElem_swapIfInBounds_of_size_le_right states:
--   (xs.swapIfInBounds i j)[k] = xs[k] given hj : xs.size ≤ j, hk : k < ...
-- V variant: uses ｢k｣ on both sides. Keeps hj (needed for truth: swap is no-op).
@[simp]
theorem getElemV_swapIfInBounds_of_size_le_right {_ : Nonempty α} {xs : Array α} {i j k : Nat}
    (hj : xs.size ≤ j) :
    (xs.swapIfInBounds i j)｢k｣ = xs｢k｣

-- #21: getElem_replace_of_ne states:
--   (xs.replace a b)[i] = xs[i] given h : i < xs.size, h' : xs[i] ≠ a
-- V variant: uses ｢i｣. Keeps h (needed for truth: out-of-bounds garbage may differ).
-- h' uses xs[i] which requires h anyway; in V form use xs｢i｣ ≠ a but keep h for truth.
theorem getElemV_replace_of_ne {_ : Nonempty α} [BEq α] [LawfulBEq α] {xs : Array α}
    {a b : α} {i : Nat} (h : i < xs.size) (h' : xs｢i｣ ≠ a) :
    (xs.replace a b)｢i｣ = xs｢i｣
```

### `Erase.lean` (3 lemmas)

| # | V lemma | Counterpart | Annotation |
|---|---------|-------------|------------|
| 23 | `mem_eraseIdx_iff_getElemV` | `mem_eraseIdx_iff_getElem` (line 423) | none |
| 24 | `getElemV_eraseIdx_of_lt` | `getElem_eraseIdx_of_lt` (line 437) | none |
| 25 | `getElemV_eraseIdx_of_ge` | `getElem_eraseIdx_of_ge` (line 442) | none |

Suggested signatures:

```lean
-- #23: mem_eraseIdx_iff_getElem states:
--   x ∈ xs.eraseIdx k h ↔ ∃ i w, i ≠ k ∧ xs[i]'w = x
-- V variant drops bound proof w from existential. Keeps h (eraseIdx requires it).
theorem mem_eraseIdx_iff_getElemV {x : α} {xs : Array α} {k : Nat} {h : k < xs.size} :
    x ∈ xs.eraseIdx k h ↔ ∃ i, i ≠ k ∧ xs｢i｣ = x

-- #24: getElem_eraseIdx_of_lt states:
--   (xs.eraseIdx i)[j] = xs[j] given w : i < xs.size, h : j < (xs.eraseIdx i).size, h' : j < i
-- V variant: drops output-side bound h. Keeps w (eraseIdx requires it) and h' (needed for truth).
theorem getElemV_eraseIdx_of_lt {_ : Nonempty α} {xs : Array α} {i : Nat} (w : i < xs.size)
    {j : Nat} (h' : j < i) :
    (xs.eraseIdx i)｢j｣ = xs｢j｣

-- #25: getElem_eraseIdx_of_ge states:
--   (xs.eraseIdx i)[j] = xs[j + 1] given w : i < xs.size, h : j < ..., h' : i ≤ j
-- V variant: drops output-side bound h. Keeps w and h' (needed for truth).
theorem getElemV_eraseIdx_of_ge {_ : Nonempty α} {xs : Array α} {i : Nat} (w : i < xs.size)
    {j : Nat} (h' : i ≤ j) :
    (xs.eraseIdx i)｢j｣ = xs｢j + 1｣
```

### `DecidableEq.lean` (3 lemmas)

| # | V lemma | Counterpart | Annotation |
|---|---------|-------------|------------|
| 26 | V-form of `isEqv_iff_rel` | line 58 | none |
| 27 | V-form of `isEqv_eq_decide` | line 64 | none |
| 28 | V-form of `beq_eq_decide` | line 151 | none |

Suggested signatures:

```lean
-- #26: isEqv_iff_rel states:
--   isEqv xs ys r ↔ ∃ h : xs.size = ys.size, ∀ i (h' : i < xs.size), r (xs[i]) (ys[i]'(h ▸ h'))
-- V variant replaces xs[i]/ys[i]'(...) with xs｢i｣/ys｢i｣. Keeps size equality (needed for truth).
-- The ∀ i still needs i < xs.size bound for the statement to be true.
theorem isEqv_iff_relV [Nonempty α] {xs ys : Array α} {r : α → α → Bool} :
    Array.isEqv xs ys r ↔ ∃ h : xs.size = ys.size, ∀ (i : Nat), i < xs.size → r xs｢i｣ ys｢i｣

-- #27: isEqv_eq_decide states:
--   isEqv xs ys r = if h : xs.size = ys.size then decide (∀ i (h' : ...), r xs[i] (ys[i]'...)) else false
-- V variant replaces indexed access with ｢i｣. Keeps size check and bound.
theorem isEqv_eq_decideV [Nonempty α] (xs ys : Array α) (r : α → α → Bool) :
    Array.isEqv xs ys r =
      if xs.size = ys.size then decide (∀ (i : Nat), i < xs.size → r xs｢i｣ ys｢i｣) else false

-- #28: beq_eq_decide states:
--   (xs == ys) = if h : xs.size = ys.size then decide (∀ i (h' : ...), xs[i] == ys[i]'...) else false
-- V variant replaces indexed access with ｢i｣.
theorem beq_eq_decideV [Nonempty α] [BEq α] (xs ys : Array α) :
    (xs == ys) =
      if xs.size = ys.size then decide (∀ (i : Nat), i < xs.size → xs｢i｣ == ys｢i｣) else false
```

### `Find.lean` (~8 lemmas)

| # | V lemma | Counterpart | Annotation |
|---|---------|-------------|------------|
| 29 | `getElemV_zero_flatten` | `getElem_zero_flatten` (line 139) | `@[grind =]` |
| 30 | `mem_of_findV` | `mem_of_find?_eq_some` (line 226) | `@[grind →]` |
| 31 | `getV_find` | `get_find?_mem` (line 231) | none |
| 32 | `findIdx_getElemV` | `findIdx_getElem` (line 370) | none |
| 33 | V-form of `not_of_lt_findIdx` | line 413 | none |
| 34 | V-form of `le_findIdx_of_not` | line 421 | none |
| 35 | V-form of `lt_findIdx_of_not` | line 429 | none |
| 36 | V-form of `findIdx_eq` | line 438 | none |

Suggested signatures:

```lean
-- #29: getElem_zero_flatten states:
--   (flatten xss)[0] = (xss.findSome? fun xs => xs[0]?).get (getElem_zero_flatten.proof h)
-- LHS has proof-taking getElem (flatten xss)[0]; RHS has proof-taking Option.get.
-- V variant replaces both: (flatten xss)｢0｣ and .getV on the RHS.
@[grind =]
theorem getElemV_zero_flatten {xss : Array (Array α)} (h : 0 < xss.flatten.size) :
    haveI : Nonempty α := ⟨(xss.findSome? fun xs => xs[0]?).get (getElem_zero_flatten.proof h)⟩
    (flatten xss)｢0｣ = (xss.findSome? fun xs => xs[0]?).getV

-- #30: mem_of_find?_eq_some states: find? p xs = some a → a ∈ xs
-- No proof-taking operation in the statement. SKIP.

-- #31: get_find?_mem states: (xs.find? p).get h ∈ xs
-- Has proof-taking Option.get. V variant replaces with Option.getV.
theorem getV_find?_mem {xs : Array α} {p : α → Bool} (h : (xs.find? p).isSome) :
    haveI : Nonempty α := ⟨(xs.find? p).get h⟩
    (xs.find? p).getV ∈ xs

-- #32: findIdx_getElem states: p xs[xs.findIdx p] (with w : xs.findIdx p < xs.size)
-- V variant replaces xs[xs.findIdx p] with xs｢xs.findIdx p｣. Keeps w because
-- out-of-bounds xs｢xs.findIdx p｣ is garbage and p(garbage) may not hold.
theorem findIdx_getElemV {p : α → Bool} {xs : Array α}
    {w : xs.findIdx p < xs.size} :
    p xs｢xs.findIdx p｣

-- #33: not_of_lt_findIdx states:
--   p (xs[i]'(le_trans h findIdx_le_size)) = false  given  h : i < xs.findIdx p
-- V variant replaces xs[i]'proof with xs｢i｣. Keeps h (needed for truth).
-- i < findIdx p implies i < xs.size, so xs｢i｣ is in-bounds.
theorem not_of_lt_findIdxV {_ : Nonempty α} {p : α → Bool} {xs : Array α} {i : Nat}
    (h : i < xs.findIdx p) :
    p xs｢i｣ = false

-- #34: le_findIdx_of_not states:
--   i ≤ xs.findIdx p  given  h : i < xs.size, h2 : ∀ j (hji : j < i), p (xs[j]'...) = false
-- V variant replaces xs[j]'proof with xs｢j｣. Keeps h (needed for statement).
-- j < i < xs.size so xs｢j｣ is in-bounds.
theorem le_findIdx_of_notV {p : α → Bool} {xs : Array α} {i : Nat}
    (h : i < xs.size) (h2 : ∀ j, j < i → p xs｢j｣ = false) :
    i ≤ xs.findIdx p

-- #35: lt_findIdx_of_not states:
--   i < xs.findIdx p  given  h : i < xs.size, h2 : ∀ j (hji : j ≤ i), ¬p (xs[j]'...)
-- V variant replaces xs[j]'proof with xs｢j｣. Keeps h.
theorem lt_findIdx_of_notV {p : α → Bool} {xs : Array α} {i : Nat}
    (h : i < xs.size) (h2 : ∀ j, j ≤ i → ¬p xs｢j｣) :
    i < xs.findIdx p

-- #36: findIdx_eq states:
--   xs.findIdx p = i ↔ p xs[i] ∧ ∀ j (hji : j < i), p (xs[j]'...) = false
--   given h : i < xs.size
-- V variant replaces xs[i] and xs[j]'proof with xs｢i｣ and xs｢j｣. Keeps h.
theorem findIdxV_eq {p : α → Bool} {xs : Array α} {i : Nat}
    (h : i < xs.size) :
    haveI : Nonempty α := ⟨xs[i]'h⟩
    xs.findIdx p = i ↔ p xs｢i｣ ∧ ∀ j, j < i → p xs｢j｣ = false
```

### `Range.lean` / `MapIdx.lean` (2 lemmas)

| # | V lemma | Counterpart | Annotation |
|---|---------|-------------|------------|
| 37 | `getElemV_zipIdx` | `getElem_zipIdx` (`MapIdx.lean:130`) | `@[simp, grind =]` |
| 38 | V-form of `fst_eq_of_mem_zipIdx` | `Range.lean:295` | none |

Suggested signatures:

```lean
-- #37: getElem_zipIdx states:
--   (xs.zipIdx k)[i] = (xs[i]'(by simp_all), k + i) given h : i < (xs.zipIdx k).size
-- V variant: result type is α × Nat, need Nonempty (α × Nat). Keep h because
-- out-of-bounds Classical.ofNonempty (α × Nat) differs from (xs｢i｣, k + i).
-- When a Nat witness k+i is available, the pair can serve as Nonempty witness.
@[simp, grind =]
theorem getElemV_zipIdx {xs : Array α} {k : Nat} {i : Nat} (h : i < (xs.zipIdx k).size) :
    haveI : Nonempty (α × Nat) := ⟨(xs[i]'(by simp_all), k + i)⟩
    (xs.zipIdx k)｢i｣ = (xs｢i｣, k + i)

-- #38: fst_eq_of_mem_zipIdx states:
--   x.1 = xs[x.2 - k]'(proof) given h : x ∈ zipIdx xs k
-- V variant replaces xs[x.2 - k]'proof with xs｢x.2 - k｣. Keeps h (needed for truth).
theorem fst_eq_of_mem_zipIdxV {_ : Nonempty α} {x : α × Nat} {xs : Array α} {k : Nat}
    (h : x ∈ zipIdx xs k) :
    x.1 = xs｢x.2 - k｣
```

## Notes

- `getElemV_of_mem`: V variant states `∃ i, xs｢i｣ = a` (drops bound proof from existential).
  NOTE: This is a weaker statement because `xs｢i｣ = a` is true for garbage values too.
  The forward direction is fine (membership guarantees an in-bounds witness), but the
  `mem_iff_getElemV` biconditional is FALSE in general (garbage `xs｢i｣` for `i ≥ xs.size`
  could equal `a` without `a ∈ xs`). `mem_iff_getElemV` should instead be:
  `a ∈ xs ↔ ∃ i, i < xs.size ∧ xs｢i｣ = a`.
- `any_eq` V-form: replaces `∃ i, ∃ h, p (xs[i]'h)` with bounded `∃ i, i < xs.size ∧ p xs｢i｣`
  because the unbounded form `∃ i, p xs｢i｣` is false in general (garbage could satisfy `p`
  for out-of-bounds `i` when `xs` is empty).
- `getElemV_eraseIdx_of_lt/ge`: These retain proof hypotheses (`j < i`, `i ≤ j`) needed for
  the equation to be correct, but drop the output-side bound proof.
- `isEqv_iff_rel`/`beq_eq_decide`: V-forms replace `xs[i]`/`ys[i]'(h ▸ h')` with `xs｢i｣`/`ys｢i｣`.
  The `∀ i` quantifier still needs `i < xs.size` for truth.
- Item 29 (`getElemV_zero_flatten`): LHS has proof-taking `getElem`, RHS has proof-taking
  `Option.get`. V variant replaces both with `getElemV` and `Option.getV`.
- Item 30 (`mem_of_find?_eq_some`): No proof-taking operation in the statement. SKIP.
- Item 31 (`getV_find?_mem`): Has proof-taking `Option.get`. V variant uses `Option.getV`.
- Items 4, 9, 10, 11, 13, 14, 15, 16, 17, 18, 22 already exist in the source and should be
  removed from the gap list.

## Revised count

- Already exist: 11 lemmas (items 4, 9, 10, 11, 13, 14, 15, 16, 17, 18, 22)
- No proof-taking op / SKIP: 1 lemma (item 30)
- Actionable: 26 new V variant lemmas
