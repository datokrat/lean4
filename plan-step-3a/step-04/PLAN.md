# Step 3a.4: Vector V Lemma Parity (Remaining)

Status: good; Refinement Needed: no

## Goal

Add `getElemV` variants for Vector lemmas in files outside the scope of Step 1.2.
Step 1.2 already covers the main `getElemV` and `backV` lemmas in `Vector/Lemmas.lean`.
This step handles the remaining files and the Lemmas.lean lemmas not covered by Step 1.2.

## Conventions

- V variants use `{_ : Nonempty α}` (or the appropriate element type) as an instance parameter.
- V variants drop explicit `i < n` proof arguments; the bound is handled internally.
- Annotations on V variants match those on the proof-taking counterpart.
- For Vector, `getElem` has index type `Nat` with proof `i < n` where `n` is the type-level size.

## Files

### `Algebra.lean` (6 create)

All 6 candidates confirmed: no V variants exist, not planned in Step 1.2.

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getElemV_zero` | `getElem_zero` (line 27) | `@[simp, grind =]` | create |
| `getElemV_add` | `getElem_add` (line 37) | `@[simp, grind =]` | create |
| `getElemV_sub` | `getElem_sub` (line 65) | `@[simp, grind =]` | create |
| `getElemV_mul` | `getElem_mul` (line 86) | `@[simp, grind =]` | create |
| `getElemV_hmul` | `getElem_hmul` (line 105) | `@[simp, grind =]` | create |
| `getElemV_smul` | `getElem_smul` (line 120) | `@[simp, grind =]` | create |

**Suggested signatures:**

```lean
@[simp, grind =]
theorem getElemV_zero [Zero α] {_ : Nonempty α} (i : Nat) :
    (0 : Vector α n)｢i｣ = 0

@[simp, grind =]
theorem getElemV_add [Add α] {_ : Nonempty α} (xs ys : Vector α n) (i : Nat) :
    (xs + ys)｢i｣ = xs｢i｣ + ys｢i｣

@[simp, grind =]
theorem getElemV_sub [Sub α] {_ : Nonempty α} (xs ys : Vector α n) (i : Nat) :
    (xs - ys)｢i｣ = xs｢i｣ - ys｢i｣

@[simp, grind =]
theorem getElemV_mul [Mul α] {_ : Nonempty α} (xs ys : Vector α n) (i : Nat) :
    (xs * ys)｢i｣ = xs｢i｣ * ys｢i｣

@[simp, grind =]
theorem getElemV_hmul [HMul α β γ] {_ : Nonempty γ} (c : α) (xs : Vector β n) (i : Nat) :
    (c * xs)｢i｣ = c * xs｢i｣

@[simp, grind =]
theorem getElemV_smul [SMul α β] {_ : Nonempty β} (c : α) (xs : Vector β n) (i : Nat) :
    (c • xs)｢i｣ = c • xs｢i｣
```

Note: `getElemV_zero` has `{_ : Nonempty α}` which is inferrable from `[Zero α]`.
For `getElemV_hmul`, the Nonempty instance is on `γ` (the result type).
`getElemV_mul` must be placed in the `section mul` block (which has `attribute [local instance] instMul`).

### `Attach.lean` (3 create)

V variants retain `hn : i < n` (needed for proof terms in RHS) but replace `[i]'proof` with `｢i｣`.

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getElemV_pmap` | `getElem_pmap` (line 225) | `@[simp, grind =]` | create |
| `getElemV_attachWith` | `getElem_attachWith` (line 242) | `@[simp, grind =]` | create |
| `getElemV_attach` | `getElem_attach` (line 248) | `@[simp, grind =]` | create |

**Suggested signatures:**

```lean
@[simp, grind =]
theorem getElemV_pmap {p : α → Prop} (f : ∀ a, p a → β) {xs : Vector α n} (h : ∀ a ∈ xs, p a)
    {i : Nat} (hn : i < n) :
    haveI : Nonempty β := ⟨f (xs[i]) (h _ (by simp))⟩
    (pmap f xs h)｢i｣ = f xs｢i｣ (h _ (by simp))

@[simp, grind =]
theorem getElemV_attachWith {xs : Vector α n} {P : α → Prop} {H : ∀ a ∈ xs, P a}
    {i : Nat} (h : i < n) :
    haveI : Nonempty { x // P x } := ⟨⟨xs[i], H _ (by simp)⟩⟩
    (xs.attachWith P H)｢i｣ = ⟨xs｢i｣, H _ (by simp)⟩

@[simp, grind =]
theorem getElemV_attach {xs : Vector α n} {i : Nat} (h : i < n) :
    haveI : Nonempty { x // x ∈ xs } := ⟨⟨xs[i], by simp⟩⟩
    xs.attach｢i｣ = ⟨xs｢i｣, by simp⟩
```

Note: For Vector, the proof-taking `getElem_pmap` already uses `hn : i < n` (not
`i < (pmap f xs h).size`), so this is already in simp normal form.

### `Count.lean` — NOT APPLICABLE

- `boole_getElem_le_countP` (line 100): Uses `getElem` inside `if p xs[i] then 1 else 0` on the
  LHS of `≤`. This is not a getElem-simplification lemma — it's a bound. The statement requires
  the proof `h : i < n` to even be well-formed (the bound only holds for valid indices).
- `boole_getElem_le_count` (line 194): Same pattern.

Both candidates: **NOT APPLICABLE** (getElem appears in hypothesis position, not as a simplifiable head).

### `Erase.lean` (3 create)

- `mem_eraseIdx_iff_getElem` (line 99): Uses `getElem` inside an existential on the RHS.
  **NOT APPLICABLE** — this is a membership characterization, not a getElem simplification.

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getElemV_eraseIdx` | `getElem_eraseIdx` (line 55) | `@[grind =]` | create |
| `getElemV_eraseIdx_of_lt` | `getElem_eraseIdx_of_lt` (line 107) | none | create |
| `getElemV_eraseIdx_of_ge` | `getElem_eraseIdx_of_ge` (line 112) | none | create |

**Suggested signatures:**

```lean
@[grind =]
theorem getElemV_eraseIdx {_ : Nonempty α} {xs : Vector α n} {i : Nat} (h : i < n)
    {j : Nat} :
    (xs.eraseIdx i)｢j｣ = if j < i then xs｢j｣ else xs｢j + 1｣

theorem getElemV_eraseIdx_of_lt {_ : Nonempty α} {xs : Vector α n} {i : Nat} (w : i < n)
    {j : Nat} (h' : j < i) :
    (xs.eraseIdx i)｢j｣ = xs｢j｣

theorem getElemV_eraseIdx_of_ge {_ : Nonempty α} {xs : Vector α n} {i : Nat} (w : i < n)
    {j : Nat} (h' : i ≤ j) :
    (xs.eraseIdx i)｢j｣ = xs｢j + 1｣
```

Note: `eraseIdx` returns `Vector α (n - 1)`, so the proof-taking version needs `j < n - 1`.
The V variant drops this output-side bound: `Classical.ofNonempty : α` is the same value
regardless of which `Vector α m` it comes from, so when `j ≥ n - 1`, both sides of the
equation return the same `Classical.ofNonempty` and the equation holds.
The proof `h : i < n` is retained because `eraseIdx` takes it as an explicit argument.

### `Extract.lean` (1 create)

- `mem_extract_iff_getElem` (line 170): Uses `getElem` inside an existential on the RHS.
  **NOT APPLICABLE** — membership characterization.

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `push_extract_getElemV` | `push_extract_getElem` (line 71) | `@[simp]` | create |

**Suggested signature:**

```lean
@[simp]
theorem push_extract_getElemV {_ : Nonempty α} {xs : Vector α n} {i j : Nat} (h : j < n) :
    (xs.extract i j).push xs｢j｣ = (xs.extract (min i j) (j + 1)).cast (by omega)
```

Note: The proof `h : j < n` is still needed for the statement to be true (otherwise `xs｢j｣`
is garbage and the equation wouldn't hold). However, the original uses `xs[j]` which requires
the proof for well-formedness. With V variant we could technically drop it but the statement
would be false for out-of-range `j`. Keep the proof.

### `Find.lean` (1 create)

- `getElem_zero_flatten` at line 121 is the `getElem?` version — **NOT APPLICABLE** (no `getElem` to V-ify).
- `getElem_zero_flatten` at line 133 is the `getElem` version.

The RHS is `(xss.findSome? fun xs => xs[0]?).get (proof)`. The V variant would need to handle
this `Option.get` on the RHS. This is complex — the proof that `findSome?` returns `some` depends
on `0 < n * m`. This is actually a necessary condition, not just a well-formedness proof.

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getElemV_zero_flatten` | `getElem_zero_flatten` (line 133) | `@[grind =]` | create |

**Suggested signature:**

```lean
@[grind =]
theorem getElemV_zero_flatten {_ : Nonempty α} {xss : Vector (Vector α m) n} (h : 0 < n * m) :
    (flatten xss)｢0｣ = (xss.findSome? fun xs => xs[0]?).get (getElem_zero_flatten.proof h)
```

Note: The proof `h : 0 < n * m` is needed because it appears in the RHS
(`getElem_zero_flatten.proof h`). Cannot be dropped.

### `InsertIdx.lean` (4 create)

All 4 candidates confirmed: no V variants exist, not planned in Step 1.2.

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getElemV_insertIdx` | `getElem_insertIdx` (line 90) | `@[grind =]` | create |
| `getElemV_insertIdx_of_lt` | `getElem_insertIdx_of_lt` (line 102) | none | create |
| `getElemV_insertIdx_self` | `getElem_insertIdx_self` (line 107) | none | create |
| `getElemV_insertIdx_of_gt` | `getElem_insertIdx_of_gt` (line 112) | none | create |

**Suggested signatures:**

```lean
@[grind =]
theorem getElemV_insertIdx {xs : Vector α n} {x : α} {i k : Nat}
    (w : i ≤ n) (h : k < n + 1) :
    haveI : Nonempty α := ⟨x⟩
    (xs.insertIdx i x)｢k｣ =
      if k < i then xs｢k｣
      else if k = i then x
      else xs｢k - 1｣

theorem getElemV_insertIdx_of_lt {xs : Vector α n} {x : α} {i k : Nat}
    (w : i ≤ n) (h : k < i) :
    haveI : Nonempty α := ⟨x⟩
    (xs.insertIdx i x)｢k｣ = xs｢k｣

theorem getElemV_insertIdx_self {xs : Vector α n} {x : α} {i : Nat}
    (w : i ≤ n) :
    haveI : Nonempty α := ⟨x⟩
    (xs.insertIdx i x)｢i｣ = x

theorem getElemV_insertIdx_of_gt {xs : Vector α n} {x : α} {i k : Nat}
    (w : k ≤ n) (h : k > i) :
    haveI : Nonempty α := ⟨x⟩
    (xs.insertIdx i x)｢k｣ = xs｢k - 1｣
```

Note: `insertIdx` returns `Vector α (n + 1)`. The proofs `w : i ≤ n` are needed for `insertIdx`
itself. The proof `h : k < n + 1` in `getElemV_insertIdx` is needed for the conditional branches
to be correct. The proofs `h : k < i`, `h : k > i` are needed for the equations to hold.

### `Lemmas.lean` (remaining, NOT in Step 1.2) (3 create)

- `getElem_eq_iff` (line 901): Equivalence `xs[i] = x ↔ xs[i]? = some x`.
  **NOT APPLICABLE** — this is a characterization lemma, not a simplification.
- `getElem_push` (line 942): **APPLICABLE** — branching version not in Step 1.2
  (Step 1.2 has `getElemV_push_lt` and `getElemV_push_eq` but not the combined branching lemma).
- `getElem_singleton` (line 956): **APPLICABLE**.
- `getElem_append` (line 1798): **ALREADY PLANNED** in Step 1.2 as `getElemV_append`.
- `getElem_eq_getElem_reverse` (line 2320): Rewrites `xs[i]` to `xs.reverse[n-1-i]`.
  The V variant would be `xs｢i｣ = xs.reverse｢n-1-i｣`. **APPLICABLE** but low priority —
  this is an identity relating two getElem calls rather than simplifying one.
- `getElem_push_last` (line 3118): Same as `getElem_push_eq` (line 931). Step 1.2 already
  plans `getElemV_push_eq`. **FALSE POSITIVE / DUPLICATE**.
- `back_eq_getElem` (line 1529): Already has `backV_eq_getElemV` (line 1533).
  **FALSE POSITIVE** — V variant exists.

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getElemV_push` | `getElem_push` (line 942) | `@[grind =]` | create |
| `getElemV_singleton` | `getElem_singleton` (line 956) | `@[simp]` | create |
| `getElemV_eq_getElemV_reverse` | `getElem_eq_getElem_reverse` (line 2320) | none | create |

**Suggested signatures:**

```lean
@[grind =]
theorem getElemV_push {xs : Vector α n} {x : α} {i : Nat} (h : i < n + 1) :
    haveI : Nonempty α := ⟨x⟩
    (xs.push x)｢i｣ = if i < n then xs｢i｣ else x

@[simp]
theorem getElemV_singleton {a : α} (h : i < 1) :
    haveI : Nonempty α := ⟨a⟩
    #v[a]｢i｣ = a

theorem getElemV_eq_getElemV_reverse {_ : Nonempty α} {xs : Vector α n} {i : Nat} (h : i < n) :
    xs｢i｣ = xs.reverse｢n - 1 - i｣
```

Note: `getElemV_push` keeps `h : i < n + 1` because without it the LHS `(xs.push x)｢i｣`
returns garbage for out-of-range indices, making the equation false.
`getElemV_singleton` keeps `h : i < 1` for the same reason.
`getElemV_eq_getElemV_reverse` keeps `h : i < n` because both sides need valid indices.

### `OfFn.lean` (1 create)

`ofFn_getElem` (line 72) says `ofFn (fun i : Fin n => xs[i.val]) = xs`. The V variant would
replace the body with `xs｢i.val｣`.

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `ofFn_getElemV` | `ofFn_getElem` (line 72) | `@[simp]` | create |

**Suggested signature:**

```lean
@[simp]
theorem ofFn_getElemV {_ : Nonempty α} {xs : Vector α n} :
    Vector.ofFn (fun i : Fin n => xs｢i.val｣) = xs
```

### `Zip.lean` (1 create)

`getElem_zip` (line 191) confirmed: no V variant exists, not planned in Step 1.2.

| V lemma | Proof-taking counterpart | Annotation | Action |
|---------|-------------------------|------------|--------|
| `getElemV_zip` | `getElem_zip` (line 191) | `@[simp, grind =]` | create |

**Suggested signature:**

```lean
@[simp, grind =]
theorem getElemV_zip {_ : Nonempty (α × β)} {as : Vector α n} {bs : Vector β n} {i : Nat}
    (h : i < n) :
    (zip as bs)｢i｣ = (as｢i｣, bs｢i｣)
```

Note: The proof `h : i < n` is needed because `Classical.ofNonempty (α × β)` may differ
from `(Classical.ofNonempty α, Classical.ofNonempty β)` — making the equation false
out-of-bounds. Use `{_ : Nonempty (α × β)}` (not separate `Nonempty α` + `Nonempty β`)
to match the element type of the result vector.

## Summary

| File | Creates | Not Applicable | Already Planned | False Positive |
|------|---------|----------------|-----------------|----------------|
| Algebra.lean | 6 | 0 | 0 | 0 |
| Attach.lean | 3 | 0 | 0 | 0 |
| Count.lean | 0 | 2 | 0 | 0 |
| Erase.lean | 3 | 1 | 0 | 0 |
| Extract.lean | 1 | 1 | 0 | 0 |
| Find.lean | 1 | 1 | 0 | 0 |
| InsertIdx.lean | 4 | 0 | 0 | 0 |
| Lemmas.lean | 3 | 1 | 1 | 2 |
| OfFn.lean | 1 | 0 | 0 | 0 |
| Zip.lean | 1 | 0 | 0 | 0 |
| **Total** | **23** | **6** | **1** | **2** |
