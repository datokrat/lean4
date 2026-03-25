# Step 1.2: Vector V Lemma Parity

Status: not started

## Goal

Create 34 V variant lemmas (10 `backV` + 24 `getElemV`) in `src/Init/Data/Vector/Lemmas.lean`.

## Key conventions for Vector

- `Vector α n` encodes the size in the type, so `getElem` takes `(h : i < n)` while `getElemV` drops this proof and requires `{_ : Nonempty α}` instead.
- `back` requires `[NeZero n]`; `backV` requires `{_ : Nonempty α}` instead.
- Some proofs (e.g. `i < n` in `getElem_push_lt`) are needed to make the *statement* true, not just for well-typedness. These are kept. The V variant only drops proofs that existed purely to make the operation well-defined.
- `backV` is defined as `xs.toArray.backV` (see `Basic.lean:136`).
- `getElemV` uses the default low-priority `GetElemV` instance derived from `GetElem?`. For `Vector α n`, `xs｢i｣` returns `α` given `{_ : Nonempty α}`.
- Place each V lemma immediately after its proof-taking counterpart (or after its `back_eq_backV`/`getElem_eq_getElemV` bridge lemma if one exists nearby).
- Use `haveI : Nonempty α := ⟨...⟩` in the statement when `Nonempty α` can be derived from context but is not in scope.

## `backV` lemmas (10 create)

| # | V lemma | Counterpart | Annotation | Suggested signature |
|---|---------|-------------|------------|---------------------|
| 1 | `backV_singleton` | `back_singleton` (line 1464) | `@[grind =]` | `theorem backV_singleton {a : α} : haveI : Nonempty α := ⟨a⟩; #v[a].backV = a` |
| 2 | `backV_eq_getElemV` | `back_eq_getElem` (line 1466) | `@[grind =]` | `theorem backV_eq_getElemV {_ : Nonempty α} {xs : Vector α n} : xs.backV = xs｢n - 1｣` |
| 3 | `backV_mem` | `back_mem` (line 1482) | `@[simp]` | `theorem backV_mem {_ : Nonempty α} [NeZero n] {xs : Vector α n} : xs.backV ∈ xs` |
| 4 | `backV_pop` | `back_pop` (line 2734) | none | `theorem backV_pop {_ : Nonempty α} {xs : Vector α n} [NeZero (n - 1)] : xs.pop.backV = xs｢n - 2｣` |
| 5 | `backV_append_of_neZero` | `back_append_of_neZero` (line 2584) | `@[simp]` | `theorem backV_append_of_neZero {_ : Nonempty α} {xs : Vector α n} {ys : Vector α m} [NeZero m] : (xs ++ ys).backV = ys.backV` |
| 6 | `backV_append` | `back_append` (line 2591) | `@[grind =]` | `theorem backV_append {_ : Nonempty α} {xs : Vector α n} {ys : Vector α m} [NeZero (n + m)] : (xs ++ ys).backV = if m = 0 then xs.backV else ys.backV` |
| 7 | `backV_append_right` | (no direct counterpart) | none | `theorem backV_append_right {_ : Nonempty α} {xs : Vector α n} {ys : Vector α (m + 1)} : (xs ++ ys).backV = ys.backV` |
| 8 | `backV_append_left` | (no direct counterpart) | none | `theorem backV_append_left {_ : Nonempty α} {xs : Vector α (n + 1)} : (xs ++ (#v[] : Vector α 0)).backV = xs.backV` |
| 9 | `backV_replicate` | `back_replicate` (line 2639) | `@[simp]` | `theorem backV_replicate {_ : Nonempty α} [NeZero n] : (replicate n a).backV = a` |
| 10 | `push_pop_backV` | `push_pop_back` (line 2987) | `@[simp]` | `theorem push_pop_backV {_ : Nonempty α} (xs : Vector α (n + 1)) : xs.pop.push xs.backV = xs` |

### Notes on `backV` lemmas

- **`backV_mem` (3)**: Retains `[NeZero n]` because membership in an empty vector is vacuously false; the `Nonempty α` alone does not help. We need `n ≠ 0` to make the statement true.
- **`backV_pop` (4)**: Retains `[NeZero (n - 1)]` from the counterpart; the RHS uses `getElemV` (not `getElem`) so no bound proof is needed on the RHS.
- **`backV_append` (6)**: The `dite` in the counterpart becomes a plain `if` since neither branch needs a proof argument for `backV`.
- **`backV_append_right` (7)** and **`backV_append_left` (8)**: No direct counterparts exist. These are convenience lemmas. The size constraints (`m + 1`, `#v[]`) ensure the statement is true without extra hypotheses.
- **`push_pop_backV` (10)**: Note the name is `push_pop_backV` (not `backV_push_pop`) to match the counterpart `push_pop_back`.
- **`backV_replicate` (9)**: Retains `[NeZero n]` because `replicate 0 a` has no back element.

## `getElemV` lemmas (24 create)

| # | V lemma | Counterpart | Annotation | Suggested signature |
|---|---------|-------------|------------|---------------------|
| 1 | `getElemV_mk` | `getElem_mk` (line 52) | `@[simp]` | `theorem getElemV_mk {_ : Nonempty α} {xs : Array α} {size : xs.size = n} {i : Nat} (h : i < n) : (Vector.mk xs size)｢i｣ = xs｢i｣` |
| 2 | `getElemV_toList` | `getElem_toList` (line 557) | `@[simp]` | `theorem getElemV_toList {_ : Nonempty α} {xs : Vector α n} {i : Nat} (h : i < xs.toList.length) : xs.toList｢i｣ = xs｢i｣` |
| 3 | `getElemV_cast` | `getElem_cast` (line 793) | `@[simp]` | `theorem getElemV_cast {_ : Nonempty α} {xs : Vector α n} {h : n = m} {i : Nat} : (xs.cast h)｢i｣ = xs｢i｣` |
| 4 | `getElem?_eq_getElemV` | `getElem?_eq_getElem` (line 862) | `@[simp]` | `theorem getElem?_eq_getElemV {_ : Nonempty α} {xs : Vector α n} {i : Nat} (h : i < n) : xs[i]? = some xs｢i｣` |
| 5 | `getElemV_push_lt` | `getElem_push_lt` (line 900) | `@[simp]` | `theorem getElemV_push_lt {_ : Nonempty α} {xs : Vector α n} {x : α} {i : Nat} (h : i < n) : (xs.push x)｢i｣ = xs｢i｣` |
| 6 | `getElemV_push_eq` | `getElem_push_eq` (line 906) | `@[simp]` | `theorem getElemV_push_eq {_ : Nonempty α} {xs : Vector α n} {x : α} : (xs.push x)｢n｣ = x` |
| 7 | `getElemV_mem` | `getElem_mem` (line 934) | `@[simp]` | `theorem getElemV_mem {_ : Nonempty α} {xs : Vector α n} {i : Nat} (h : i < n) : xs｢i｣ ∈ xs` |
| 8 | `getElemV_set` | `getElem_set` (line 1293) | `@[grind =]` | `theorem getElemV_set {_ : Nonempty α} {xs : Vector α n} {i : Nat} {x : α} (hi : i < n) {j : Nat} : (xs.set i x hi)｢j｣ = if i = j then x else xs｢j｣` |
| 9 | `getElemV_set_self` | `getElem_set_self` (line 1298) | `@[simp]` | `theorem getElemV_set_self {_ : Nonempty α} {xs : Vector α n} {i : Nat} {x : α} (hi : i < n) : (xs.set i x hi)｢i｣ = x` |
| 10 | `getElemV_set_ne` | `getElem_set_ne` (line 1303) | `@[simp]` | `theorem getElemV_set_ne {_ : Nonempty α} {xs : Vector α n} {x : α} (hi : i < n) (h : i ≠ j) : (xs.set i x hi)｢j｣ = xs｢j｣` |
| 11 | `set_getElemV_self` | `set_getElem_self` (line 1318) | `@[simp]` | `theorem set_getElemV_self {_ : Nonempty α} {xs : Vector α n} (hi : i < n) : xs.set i xs｢i｣ hi = xs` |
| 12 | `getElemV_setIfInBounds` | `getElem_setIfInBounds` (line 1354) | `@[grind =]` | `theorem getElemV_setIfInBounds {_ : Nonempty α} {xs : Vector α n} {x : α} {j : Nat} (hj : j < n) : (xs.setIfInBounds i x)｢j｣ = if i = j then x else xs｢j｣` |
| 13 | `getElemV_setIfInBounds_self` | `getElem_setIfInBounds_self` (line 1359) | `@[simp]` | `theorem getElemV_setIfInBounds_self {_ : Nonempty α} {xs : Vector α n} {x : α} (hi : i < n) : (xs.setIfInBounds i x)｢i｣ = x` |
| 14 | `getElemV_setIfInBounds_ne` | `getElem_setIfInBounds_ne` (line 1364) | `@[simp]` | `theorem getElemV_setIfInBounds_ne {_ : Nonempty α} {xs : Vector α n} {x : α} (hj : j < n) (h : i ≠ j) : (xs.setIfInBounds i x)｢j｣ = xs｢j｣` |
| 15 | `getElemV_flatten` | `getElem_flatten` (line 1916) | `@[simp]` | `theorem getElemV_flatten {_ : Nonempty β} {xss : Vector (Vector β m) n} {i : Nat} (hi : i < n * m) : xss.flatten｢i｣ = (haveI : i / m < n := by rwa [Nat.div_lt_iff_lt_mul (Nat.pos_of_lt_mul_left hi)]; xss｢i / m｣)｢i % m｣` |
| 16 | `getElemV_flatMap` | `getElem_flatMap` (line 2049) | `@[simp]` | `theorem getElemV_flatMap {_ : Nonempty β} {xs : Vector α n} {f : α → Vector β m} {i : Nat} (hi : i < n * m) : (xs.flatMap f)｢i｣ = (haveI : i / m < n := by rwa [Nat.div_lt_iff_lt_mul (Nat.pos_of_lt_mul_left hi)]; (f xs｢i / m｣))｢i % m｣` |
| 17 | `getElemV_extract` | `getElem_extract` (line 2316) | `@[simp]` | `theorem getElemV_extract {_ : Nonempty α} {as : Vector α n} {start stop : Nat} (h : i < min stop n - start) : (as.extract start stop)｢i｣ = as｢start + i｣` |
| 18 | `getElemV_pop'` | `getElem_pop'` (line 2725) | `@[simp]` | `theorem getElemV_pop' {_ : Nonempty α} {xs : Vector α (n + 1)} {i : Nat} (h : i < n) : xs.pop｢i｣ = xs｢i｣` |
| 19 | `getElemV_replace` | `getElem_replace` (line 2930) | `@[grind =]` | `theorem getElemV_replace {_ : Nonempty α} [BEq α] [LawfulBEq α] {xs : Vector α n} {i : Nat} (h : i < n) : (xs.replace a b)｢i｣ = if xs｢i｣ == a then if a ∈ xs.take i then a else b else xs｢i｣` |
| 20 | `getElemV_swap` | `getElem_swap` (line 3021) | `@[grind =]` | `theorem getElemV_swap {_ : Nonempty α} {xs : Vector α n} {i j : Nat} (hi : i < n) (hj : j < n) {k : Nat} : (xs.swap i j hi hj)｢k｣ = if k = i then xs｢j｣ else if k = j then xs｢i｣ else xs｢k｣` |
| 21 | `getElemV_swap_right` | `getElem_swap_right` (line 3026) | `@[simp]` | `theorem getElemV_swap_right {_ : Nonempty α} {xs : Vector α n} {i j : Nat} (hi : i < n) (hj : j < n) : (xs.swap i j hi hj)｢j｣ = xs｢i｣` |
| 22 | `getElemV_swap_left` | `getElem_swap_left` (line 3030) | `@[simp]` | `theorem getElemV_swap_left {_ : Nonempty α} {xs : Vector α n} {i j : Nat} (hi : i < n) (hj : j < n) : (xs.swap i j hi hj)｢i｣ = xs｢j｣` |
| 23 | `getElemV_swap_of_ne` | `getElem_swap_of_ne` (line 3034) | `@[simp]` | `theorem getElemV_swap_of_ne {_ : Nonempty α} {xs : Vector α n} {i j : Nat} {hi : i < n} {hj : j < n} {k : Nat} (hi' : k ≠ i) (hj' : k ≠ j) : (xs.swap i j hi hj)｢k｣ = xs｢k｣` |
| 24 | `getElemV_drop` | `getElem_drop` (line 3065) | `@[grind =]` | `theorem getElemV_drop {_ : Nonempty α} {xs : Vector α n} {j : Nat} (hi : i < n - j) : (xs.drop j)｢i｣ = xs｢j + i｣` |

### Notes on `getElemV` lemmas

- **Bound proofs retained for statement truth**: Many `getElemV` lemmas retain bound proofs (e.g. `h : i < n`) because without them the statement would not hold -- `getElemV` returns `Classical.ofNonempty` when out of bounds, so the equality would be false. For instance, `getElemV_push_lt` needs `i < n` to guarantee that `(xs.push x)｢i｣` actually equals `xs｢i｣` rather than garbage.
- **Bound proofs retained for `set`/`swap`**: The `hi : i < n` proofs on `set` and `swap` are required by the *operation itself* (Vector's `set` takes a proof), not just by `getElem`. These are always kept.
- **`getElemV_mk` (1)**: Keeps `h : i < n` because `Vector.mk xs size` uses the array's indexing, and out-of-bounds would give garbage.
- **`getElemV_toList` (2)**: Keeps `h : i < xs.toList.length` for the same reason -- both sides need to be in-bounds for equality.
- **`getElemV_cast` (3)**: No bound proof needed; `cast` preserves content and `getElemV` handles out-of-bounds uniformly on both sides.
- **`getElem?_eq_getElemV` (4)**: Named with `getElem?` prefix since the LHS is `getElem?`; keeps `h : i < n` because `getElem?` returns `some` only when in bounds.
- **`getElemV_flatten` (15)** and **`getElemV_flatMap` (16)**: Keep `hi : i < n * m` because the RHS indexes into inner vectors and the equality only holds in-bounds. The `haveI` blocks derive division/modulus bounds.
- **`getElemV_pop'` (18)**: Uses `h : i < n` (simplified from `i < n + 1 - 1`).
- **`getElemV_replace` (19)**: Needs `[BEq α] [LawfulBEq α]` from the counterpart. Keeps `h : i < n` for statement truth.
- **`set_getElemV_self` (11)**: The `xs｢i｣` on the LHS uses `getElemV`; keeps `hi : i < n` because `set` requires it. The statement says setting element `i` to its own value is a no-op.

## Proof strategy

Most proofs follow the pattern:
```lean
theorem backV_foo {_ : Nonempty α} ... : ... := by
  simp [back_eq_backV, back_foo]
```
or
```lean
theorem getElemV_foo {_ : Nonempty α} ... : ... := by
  simp [getElemV_def, getElem_foo]
```

For lemmas where `getElemV_def` unfolds to a `match` on `getElem?`, an alternative is:
```lean
  rw [show xs｢i｣ = xs[i] from getElem_eq_getElemV ..]
  exact getElem_foo ..
```

## Implementation order

1. `backV` lemmas (1-10), placed after the existing `back` lemmas in their respective sections
2. `getElemV` lemmas (1-14), placed in the `set`/`push`/`mem` sections
3. `getElemV` lemmas (15-24), placed in the `flatten`/`extract`/`pop`/`replace`/`swap`/`drop` sections
