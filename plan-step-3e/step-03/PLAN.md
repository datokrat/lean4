# Step 3e.3: Vector V Lemma Parity (Full Audit)

Status: not started; Refinement Needed: no

## Files

Multiple files under `src/Init/Data/Vector/`.

## ACTIONABLE GAPS — V variants to create

| # | V lemma | File | Counterpart | Annotation |
|---|---------|------|-------------|------------|
| 1 | `getElemV_neg` | Algebra.lean | `getElem_neg` (line 60) | `@[simp, grind =]` |
| 2 | `getElemV_append_left` | Lemmas.lean | `getElem_append_left` (line 1816) | `@[simp]` |
| 3 | `getElemV_append_right` | Lemmas.lean | `getElem_append_right` (line 1820) | `@[simp]` |
| 4 | `getElemV_pop'` | Lemmas.lean | `getElem_pop'` (line 2858) | none |
| 5 | `getElemV_of_mem` | Lemmas.lean | `getElem_of_mem` (line 1112) | none |
| 6 | `getElemV?_of_mem` | Lemmas.lean | `getElem?_of_mem` (line 1116) | none |
| 7 | `getElemV_modify` | Lemmas.lean | (proof-taking modify lemma) | none |
| 8 | `boole_getElemV_le_countP` | Count.lean | `boole_getElem_le_countP` (line 100) | none |
| 9 | `boole_getElemV_le_count` | Count.lean | `boole_getElem_le_count` (line 194) | none |
| 10 | `getElemV?_extract_of_lt` | Extract.lean | `getElem?_extract_of_lt` (line 91) | `@[simp]` |
| 11 | `getElemV?_eraseIdx_of_lt` | Erase.lean | `getElem?_eraseIdx_of_lt` (line 42) | none |
| 12 | `getElemV?_eraseIdx_of_ge` | Erase.lean | `getElem?_eraseIdx_of_ge` (line 47) | none |
| 13 | `backV_filter_of_pos` | Find.lean | `back_filter_of_pos` (if exists) | none |
| 14 | `backV_filterMap_of_eq_some` | Find.lean | `back_filterMap_of_eq_some` (if exists) | none |

## Notes

- `getElemV_neg`: Matches the pattern of `getElemV_add/sub/mul/etc.` already created in Step 3a.4.
- `getElemV_append_left/right`: Array has these (from Step 1), List has these, Vector doesn't.
- `getElemV_of_mem`: Returns `∃ i, xs｢i｣ = a`.
- `getElemV?_*` variants: These have `getElem?` in the name but use proof-taking getElem in statement.
- `backV_filter_of_pos/filterMap_of_eq_some`: Array has these; Vector should too for consistency.
- `getElemV_pop'` (row 4): **already exists** at Lemmas.lean line 2862. Remove from scope.
- `getElemV_modify` (row 7): No `modify` operation exists on `Vector` at all. Remove from scope.
- `backV_filter_of_pos` / `backV_filterMap_of_eq_some` (rows 13–14): No `back_filter_of_pos` or `back_filterMap_of_eq_some` counterparts exist in Vector source. Remove from scope or create both the counterpart and the V variant.

## Suggested signatures

### 1. `getElemV_neg` (Algebra.lean)

Counterpart: `theorem getElem_neg [Neg α] (xs : Vector α n) (i : Nat) (h : i < n) : (-xs)[i] = -xs[i]`

```lean
@[simp, grind =]
theorem getElemV_neg [Neg α] {_ : Nonempty α} (xs : Vector α n) (i : Nat) :
    (-xs)｢i｣ = -xs｢i｣
```

### 2. `getElemV_append_left` (Lemmas.lean)

Counterpart: `theorem getElem_append_left {xs : Vector α n} {ys : Vector α m} (hi : i < n) : (xs ++ ys)[i] = xs[i]`

```lean
@[simp]
theorem getElemV_append_left {_ : Nonempty α} {xs : Vector α n} {ys : Vector α m} (hi : i < n) :
    (xs ++ ys)｢i｣ = xs｢i｣
```

Note: `hi : i < n` is needed because the RHS is `xs｢i｣` which needs `i < n` for the equation
to hold (out-of-bounds on `xs` gives garbage, but in-bounds on `xs ++ ys` gives a real value).

### 3. `getElemV_append_right` (Lemmas.lean)

Counterpart: `theorem getElem_append_right {xs : Vector α n} {ys : Vector α m} (h : i < n + m) (hi : n ≤ i) : (xs ++ ys)[i] = ys[i - n]`

```lean
@[simp]
theorem getElemV_append_right {_ : Nonempty α} {xs : Vector α n} {ys : Vector α m} (hi : n ≤ i) :
    (xs ++ ys)｢i｣ = ys｢i - n｣
```

Note: Drop `h : i < n + m` — out-of-bounds on `xs ++ ys`, both sides return
`Classical.ofNonempty`. Keep `hi : n ≤ i` because it's needed for the equation to hold
(determines which half the index falls in).

### 4. `getElemV_pop'` — ALREADY EXISTS

`getElemV_pop'` already exists at Lemmas.lean line 2862. Remove from scope.

### 5. `getElemV_of_mem` (Lemmas.lean)

Counterpart: `theorem getElem_of_mem {a} {xs : Vector α n} (h : a ∈ xs) : ∃ (i : Nat) (h : i < n), xs[i]'h = a`

```lean
theorem getElemV_of_mem {a} {xs : Vector α n} (h : a ∈ xs) :
    haveI : Nonempty α := ⟨a⟩
    ∃ i : Nat, xs｢i｣ = a
```

Note: The witness `a : α` provides the `Nonempty` instance via `haveI`. The existential
drops the `h : i < n` — the equation holds trivially when `i ≥ n` (both sides are not
necessarily equal, so we still need some `i < n` witnesses). Actually, when `i ≥ n`,
`xs｢i｣ = Classical.ofNonempty` which may not equal `a`. So the existential implicitly
quantifies over all `i`, and the proof picks an in-bounds `i`.

### 6. `getElemV?_of_mem` (Lemmas.lean)

Counterpart: `theorem getElem?_of_mem {a} {xs : Vector α n} (h : a ∈ xs) : ∃ i : Nat, xs[i]? = some a`

This is a `getElem?` lemma, not a `getElem` lemma — there is no proof to drop and no V variant
needed. **Remove from scope.**

### 7. `getElemV_modify` — NO COUNTERPART

No `modify` operation or lemma exists on `Vector`. **Remove from scope.**

### 8. `boole_getElemV_le_countP` (Count.lean)

Counterpart: `theorem boole_getElem_le_countP {p : α → Bool} {xs : Vector α n} (h : i < n) : (if p xs[i] then 1 else 0) ≤ xs.countP p`

```lean
theorem boole_getElemV_le_countP {p : α → Bool} {xs : Vector α n}
    (h : i < n) :
    (if p xs｢i｣ then 1 else 0) ≤ xs.countP p
```

Note: Keep `h : i < n` — without it, `xs｢i｣ = Classical.ofNonempty` and the inequality
may not hold (the count doesn't account for garbage values).

### 9. `boole_getElemV_le_count` (Count.lean)

Counterpart: `theorem boole_getElem_le_count {a : α} {xs : Vector α n} (h : i < n) : (if xs[i] == a then 1 else 0) ≤ xs.count a`

```lean
theorem boole_getElemV_le_count {a : α} {xs : Vector α n} (h : i < n) :
    haveI : Nonempty α := ⟨a⟩
    (if xs｢i｣ == a then 1 else 0) ≤ xs.count a
```

Note: Keep `h : i < n` for the same reason as `boole_getElemV_le_countP`. Use `haveI`
with the witness `a`.

### 10. `getElemV?_extract_of_lt` (Extract.lean)

Counterpart: `theorem getElem?_extract_of_lt {xs : Vector α n} {i j k : Nat} (h : k < min j n - i) : (xs.extract i j)[k]? = some (xs[i + k]'(by omega))`

This is a `getElem?` lemma — the LHS is `(xs.extract i j)[k]?` which returns `Option α`.
The `getElem` on the RHS is proof-taking but wrapped in `some`. A V variant would replace
the RHS proof-taking `getElem` with `getElemV`:

```lean
@[simp]
theorem getElemV?_extract_of_lt {_ : Nonempty α} {xs : Vector α n} {i j k : Nat}
    (h : k < min j n - i) :
    (xs.extract i j)[k]? = some xs｢i + k｣
```

### 11. `getElemV?_eraseIdx_of_lt` (Erase.lean)

Counterpart: `theorem getElem?_eraseIdx_of_lt {xs : Vector α n} {i : Nat} (h : i < n) {j : Nat} (h' : j < i) : (xs.eraseIdx i)[j]? = xs[j]?`

The LHS and RHS are both `getElem?` — no proof-taking `getElem` to V-ify. **Remove from scope.**

### 12. `getElemV?_eraseIdx_of_ge` (Erase.lean)

Counterpart: `theorem getElem?_eraseIdx_of_ge {xs : Vector α n} {i : Nat} (h : i < n) {j : Nat} (h' : i ≤ j) : (xs.eraseIdx i)[j]? = xs[j + 1]?`

Same as above — both sides are `getElem?`. **Remove from scope.**

### 13. `backV_filter_of_pos` (Find.lean)

No counterpart `back_filter_of_pos` exists in Vector source files. **Remove from scope**
(or create counterpart first in a separate step).

### 14. `backV_filterMap_of_eq_some` (Find.lean)

No counterpart `back_filterMap_of_eq_some` exists in Vector source files. **Remove from scope**
(or create counterpart first in a separate step).

## Revised scope

After audit, only **6** of the original 14 are actionable V variant lemmas:

| # | V lemma | File |
|---|---------|------|
| 1 | `getElemV_neg` | Algebra.lean |
| 2 | `getElemV_append_left` | Lemmas.lean |
| 3 | `getElemV_append_right` | Lemmas.lean |
| 5 | `getElemV_of_mem` | Lemmas.lean |
| 8 | `boole_getElemV_le_countP` | Count.lean |
| 9 | `boole_getElemV_le_count` | Count.lean |

Plus **1** mixed variant (replaces proof-taking `getElem` on the RHS of a `getElem?` lemma):

| # | V lemma | File |
|---|---------|------|
| 10 | `getElemV?_extract_of_lt` | Extract.lean |

**Removed** (8 items):
- Row 4 (`getElemV_pop'`): already exists
- Row 6 (`getElemV?_of_mem`): pure `getElem?` lemma, nothing to V-ify
- Row 7 (`getElemV_modify`): no `modify` on Vector
- Rows 11–12 (`getElemV?_eraseIdx_of_lt/ge`): pure `getElem?` lemmas
- Rows 13–14 (`backV_filter_of_pos`, `backV_filterMap_of_eq_some`): no counterparts exist

## Total: 7 new V variant lemmas
