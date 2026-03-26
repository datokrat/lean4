# Step 3a.5: BitVec V Lemma Parity

Status: good; Refinement Needed: no

## Files

`src/Init/Data/BitVec/Basic.lean`, `src/Init/Data/BitVec/Lemmas.lean`,
`src/Init/Data/BitVec/Bitblast.lean`, `src/Init/Data/BitVec/Bootstrap.lean`

## Context

BitVec uses `getElem` to access individual bits: `(x : BitVec w)[i]` where `i < w`.
The element type is `Bool`, which is `Inhabited` and therefore `Nonempty`.

**Critical prerequisite**: There is currently no `GetElemV (BitVec w) Nat Bool` instance.
One must be added before any V variant lemmas can be defined.

Since `Bool` is always `Nonempty` (via `Inhabited Bool`), the `{_ : Nonempty Bool}` parameter
is always automatically inferred. The V variant lemmas therefore do not need an explicit
`Nonempty` binder — it is satisfied by typeclass inference in all cases.

The V variant lemmas should:
- Replace `x[i]` (which requires `i < w`) with `x｢i｣` (which only requires `Nonempty Bool`)
- Drop the explicit `(h : i < w)` proof parameter
- Retain the same `@[simp]`/`@[grind =]` annotations as the original
- RHS occurrences of `x[j]` with bounded indexing should also become `x｢j｣` when the bound
  is not available from other hypotheses

## Step 0: Add `GetElemV` and `LawfulGetElemV` instances

In `src/Init/Data/BitVec/Basic.lean`, after the existing `GetElem` instance (line 116),
add:

```lean
noncomputable instance : GetElemV (BitVec w) Nat Bool where
  getElemV x i := if h : i < w then x[i] else Classical.ofNonempty

instance : LawfulGetElemV (BitVec w) Nat Bool fun _ i => i < w where
  getElemV_def x i := by
    simp only [getElemV, getElem?, decidableGetElem?]
    split <;> rfl
```

Also add an `@[simp, grind =]` bridge lemma:

```lean
@[simp, grind =] theorem getElemV_eq_getLsbD {x : BitVec w} {i : Nat} :
    x｢i｣ = x.getLsbD i := by
  simp [getElemV_def, getElem?_def, getLsbD_eq_getElem?_getD]
  split <;> simp_all
```

## Confirmed candidates

### `Bootstrap.lean`

#### 1. `getElem_setWidth'` (line 116) — `@[grind =]`

Source signature:
```lean
theorem getElem_setWidth' (x : BitVec w) (i : Nat) (h : w ≤ v) (hi : i < v) :
    (setWidth' h x)[i] = x.getLsbD i
```

V variant:
```lean
@[grind =]
theorem getElemV_setWidth' (x : BitVec w) (i : Nat) (h : w ≤ v) :
    (setWidth' h x)｢i｣ = x.getLsbD i
```

Note: `h : w ≤ v` is retained because it is needed for `setWidth'` to type-check.

#### 2. `getElem_setWidth` (line 121) — `@[simp, grind =]`

Source signature:
```lean
theorem getElem_setWidth (m : Nat) (x : BitVec n) (i : Nat) (h : i < m) :
    (setWidth m x)[i] = x.getLsbD i
```

V variant:
```lean
@[simp, grind =]
theorem getElemV_setWidth (m : Nat) (x : BitVec n) (i : Nat) :
    (setWidth m x)｢i｣ = x.getLsbD i
```

### `Lemmas.lean`

#### 3. `getElem_ofBool_zero` (line 432) — `@[simp, grind =]`

Source signature:
```lean
theorem getElem_ofBool_zero {b : Bool} : (ofBool b)[0] = b
```

V variant:
```lean
@[simp, grind =]
theorem getElemV_ofBool_zero {b : Bool} : (ofBool b)｢0｣ = b
```

#### 4. `getElem_ofBool` (line 451) — `@[simp]`

Source signature:
```lean
theorem getElem_ofBool {b : Bool} {h : i < 1} : (ofBool b)[i] = b
```

V variant:
```lean
@[simp]
theorem getElemV_ofBool {b : Bool} : (ofBool b)｢i｣ = ((i = 0) && b)
```

Note: Without the `i < 1` bound, we cannot guarantee `i = 0`, so the RHS must handle
the out-of-bounds case. The `getElemV_def` will resolve to `getLsbD` which equals
`(i = 0) && b` (matching `getLsbD_ofBool`). Alternatively this could be stated as
`= x.getLsbD i` but the expanded form is more useful for `simp`.

#### 5. `getElem_shiftLeft` (line 1874) — `@[simp, grind =]`

Source signature:
```lean
theorem getElem_shiftLeft {x : BitVec m} {n : Nat} (h : i < m) :
    (x <<< n)[i] = (!decide (i < n) && x[i - n])
```

V variant:
```lean
@[simp, grind =]
theorem getElemV_shiftLeft {x : BitVec m} {n : Nat} :
    (x <<< n)｢i｣ = (!decide (i < n) && x｢i - n｣)
```

Note: Both LHS and RHS `getElem` become `getElemV`.

#### 6. `getElem_shiftLeft'` (line 2052) — no annotation

Source signature:
```lean
theorem getElem_shiftLeft' {x : BitVec w₁} {y : BitVec w₂} {i : Nat} (h : i < w₁) :
    (x <<< y)[i] = (!decide (i < y.toNat) && x[i - y.toNat])
```

V variant:
```lean
theorem getElemV_shiftLeft' {x : BitVec w₁} {y : BitVec w₂} {i : Nat} :
    (x <<< y)｢i｣ = (!decide (i < y.toNat) && x｢i - y.toNat｣)
```

#### 7. `getElem_sshiftRight` (line 2279) — `@[grind =]`

Source signature:
```lean
theorem getElem_sshiftRight {x : BitVec w} {s i : Nat} (h : i < w) :
    (x.sshiftRight s)[i] = (if h : s + i < w then x[s + i] else x.msb)
```

V variant:
```lean
@[grind =]
theorem getElemV_sshiftRight {x : BitVec w} {s i : Nat} :
    (x.sshiftRight s)｢i｣ = (if s + i < w then x｢s + i｣ else x.msb)
```

Note: The `dif` on `h : s + i < w` in the original is used by the inner `x[s+i]`;
in the V variant it becomes a plain `if` since `x｢s+i｣` doesn't need a proof.
When `i ≥ w`, `getElemV` returns `Classical.ofNonempty` — the proof must handle this
out-of-bounds case. The LHS resolves to `getLsbD (sshiftRight ..) i` which equals
`!decide (w ≤ i) && (if s+i < w then .. else msb)`. When `w ≤ i`, this is `false`,
but `Classical.ofNonempty` for `Bool` could be either value. **Flag: needs careful
proof — the out-of-bounds behavior of `getElemV` must match `getLsbD`.**

Revised approach: Since `getElemV_def` says `x｢i｣ = (x[i]?).getD Classical.ofNonempty`
and `x[i]? = none` when `i ≥ w`, the LHS when `i ≥ w` equals `Classical.ofNonempty`.
The RHS would be `if s + i < w then ... else x.msb` — when `i ≥ w`, if `s + i ≥ w`
(always true), this is `x.msb`. So `Classical.ofNonempty = x.msb` — not provable.

**This lemma requires `i < w` in the hypothesis to make the statement true.
Therefore the V variant should retain a hypothesis, or use `getLsbD` form on the RHS.**

Alternative V variant:
```lean
@[grind =]
theorem getElemV_sshiftRight {x : BitVec w} {s i : Nat} :
    (x.sshiftRight s)｢i｣ = x.getLsbD (sshiftRight_getLsbD_index w s i)
```

This is awkward. Better to keep the proof:
```lean
@[grind =]
theorem getElemV_sshiftRight {x : BitVec w} {s i : Nat} (h : i < w) :
    (x.sshiftRight s)｢i｣ = (if s + i < w then x｢s + i｣ else x.msb)
```

The `h : i < w` is needed for the statement to be meaningful (not for indexing).

#### 8. `getElem_sshiftRight'` (line 2498) — no annotation

Source signature:
```lean
theorem getElem_sshiftRight' {x y : BitVec w} {i : Nat} (h : i < w) :
    (x.sshiftRight' y)[i] = (if h : y.toNat + i < w then x[y.toNat + i] else x.msb)
```

Same situation as `getElem_sshiftRight` — needs `h : i < w`.

V variant:
```lean
theorem getElemV_sshiftRight' {x y : BitVec w} {i : Nat} (h : i < w) :
    (x.sshiftRight' y)｢i｣ = (if y.toNat + i < w then x｢y.toNat + i｣ else x.msb)
```

#### 9. `getElem_signExtend` (line 2573) — `@[grind =]`

Source signature:
```lean
theorem getElem_signExtend {x : BitVec w} {v i : Nat} (h : i < v) :
    (x.signExtend v)[i] = if h : i < w then x[i] else x.msb
```

V variant:
```lean
@[grind =]
theorem getElemV_signExtend {x : BitVec w} {v i : Nat} :
    (x.signExtend v)｢i｣ = if i < w then x｢i｣ else x.msb
```

**Flag: same out-of-bounds issue.** When `i ≥ v`, `(signExtend v x)｢i｣` is
`Classical.ofNonempty` but the RHS depends on `i < w` vs `i ≥ w`. Needs `h : i < v`:

```lean
@[grind =]
theorem getElemV_signExtend {x : BitVec w} {v i : Nat} (h : i < v) :
    (x.signExtend v)｢i｣ = if i < w then x｢i｣ else x.msb
```

#### 10. `getElem_append` (line 2757) — `@[grind =]`

Source signature:
```lean
theorem getElem_append {x : BitVec n} {y : BitVec m} (h : i < n + m) :
    (x ++ y)[i] = if h : i < m then y[i] else x[i - m]
```

V variant:
```lean
@[grind =]
theorem getElemV_append {x : BitVec n} {y : BitVec m} :
    (x ++ y)｢i｣ = if i < m then y｢i｣ else x｢i - m｣
```

**Flag: out-of-bounds issue.** When `i ≥ n + m`, LHS is `Classical.ofNonempty` but
RHS depends on `i < m`. If `i ≥ m`, RHS = `x｢i - m｣` which is also
`Classical.ofNonempty` when `i - m ≥ n`. So both sides would be `Classical.ofNonempty`
— but we can't prove they're equal since `Classical.ofNonempty` is opaque.

Needs `h : i < n + m`:
```lean
@[grind =]
theorem getElemV_append {x : BitVec n} {y : BitVec m} (h : i < n + m) :
    (x ++ y)｢i｣ = if i < m then y｢i｣ else x｢i - m｣
```

#### 11. `getElem_concat` (line 3336) — `@[grind =]`

Source signature:
```lean
theorem getElem_concat (x : BitVec w) (b : Bool) (i : Nat) (h : i < w + 1) :
    (concat x b)[i] = if h : i = 0 then b else x[i - 1]
```

V variant (needs `h : i < w + 1` for same reason as `append`):
```lean
@[grind =]
theorem getElemV_concat (x : BitVec w) (b : Bool) (i : Nat) (h : i < w + 1) :
    (concat x b)｢i｣ = if i = 0 then b else x｢i - 1｣
```

#### 12. `getElem_shiftConcat` (line 3452) — `@[grind =]`

Source signature:
```lean
theorem getElem_shiftConcat {x : BitVec w} {b : Bool} (h : i < w) :
    (x.shiftConcat b)[i] = if i = 0 then b else x[i-1]
```

V variant:
```lean
@[grind =]
theorem getElemV_shiftConcat {x : BitVec w} {b : Bool} (h : i < w) :
    (x.shiftConcat b)｢i｣ = if i = 0 then b else x｢i - 1｣
```

Note: `h : i < w` is needed because `shiftConcat` has width `w`, and the RHS
references `x[i-1]` which needs `i - 1 < w`.

#### 13. `getElem_shiftConcat_zero` (line 3457) — `@[simp]`

Source signature:
```lean
theorem getElem_shiftConcat_zero {x : BitVec w} (b : Bool) (h : 0 < w) :
    (x.shiftConcat b)[0] = b
```

V variant:
```lean
@[simp]
theorem getElemV_shiftConcat_zero {x : BitVec w} (b : Bool) (h : 0 < w) :
    (x.shiftConcat b)｢0｣ = b
```

Note: `h : 0 < w` is needed for the statement to be true (when `w = 0`,
`shiftConcat` produces a 0-width bitvec and `getElemV` returns `Classical.ofNonempty`).

#### 14. `getElem_shiftConcat_succ` (line 3462) — `@[simp]`

Source signature:
```lean
theorem getElem_shiftConcat_succ {x : BitVec w} {b : Bool} (h : i + 1 < w) :
    (x.shiftConcat b)[i+1] = x[i]
```

V variant:
```lean
@[simp]
theorem getElemV_shiftConcat_succ {x : BitVec w} {b : Bool} (h : i + 1 < w) :
    (x.shiftConcat b)｢i + 1｣ = x｢i｣
```

Note: `h : i + 1 < w` is needed so that the statement is true.

#### 15. `getElem_fill` (line 3914) — `@[simp, grind =]`

Source signature:
```lean
theorem getElem_fill {w i : Nat} {v : Bool} (h : i < w) :
    (fill w v)[i] = v
```

V variant (needs `h : i < w` since out-of-bounds returns `Classical.ofNonempty ≠ v` in general):
```lean
@[simp, grind =]
theorem getElemV_fill {w i : Nat} {v : Bool} (h : i < w) :
    (fill w v)｢i｣ = v
```

#### 16. `getElem_rotateLeft` (line 4874) — `@[simp, grind =]`

Source signature:
```lean
theorem getElem_rotateLeft {x : BitVec w} {r i : Nat} (h : i < w) :
    (x.rotateLeft r)[i] =
      if h' : i < r % w then x[(w - (r % w) + i)] else x[i - (r % w)]
```

V variant:
```lean
@[simp, grind =]
theorem getElemV_rotateLeft {x : BitVec w} {r i : Nat} (h : i < w) :
    (x.rotateLeft r)｢i｣ =
      if i < r % w then x｢w - (r % w) + i｣ else x｢i - (r % w)｣
```

Note: `h : i < w` needed for truthfulness; the inner `getElem` indices are bounded
by `i < w` and properties of `%`, so they become `getElemV` safely.

#### 17. `getElem_rotateRight` (line 5042) — `@[simp, grind =]`

Source signature:
```lean
theorem getElem_rotateRight {x : BitVec w} {r i : Nat} (h : i < w) :
    (x.rotateRight r)[i] = if h' : i < w - (r % w) then x[(r % w) + i] else x[(i - (w - (r % w)))]
```

V variant:
```lean
@[simp, grind =]
theorem getElemV_rotateRight {x : BitVec w} {r i : Nat} (h : i < w) :
    (x.rotateRight r)｢i｣ =
      if i < w - (r % w) then x｢(r % w) + i｣ else x｢i - (w - (r % w))｣
```

#### 18. `getElem_twoPow` (line 5188) — `@[simp, grind =]`

Source signature:
```lean
theorem getElem_twoPow {i j : Nat} (h : j < w) : (twoPow w i)[j] = decide (j = i)
```

V variant (needs `h : j < w`):
```lean
@[simp, grind =]
theorem getElemV_twoPow {i j : Nat} (h : j < w) : (twoPow w i)｢j｣ = decide (j = i)
```

#### 19. `getElem_replicate` (line 5361) — `@[simp, grind =]`

Source signature:
```lean
theorem getElem_replicate {n w : Nat} {x : BitVec w} (h : i < w * n) :
    (x.replicate n)[i] = if h' : w = 0 then false else x[i % w]'(Nat.mod_lt i (by omega))
```

V variant:
```lean
@[simp, grind =]
theorem getElemV_replicate {n w : Nat} {x : BitVec w} (h : i < w * n) :
    (x.replicate n)｢i｣ = if w = 0 then false else x｢i % w｣
```

#### 20. `getElem_abs` (line 5779) — `@[grind =]`

Source signature:
```lean
theorem getElem_abs {i : Nat} {x : BitVec w} (h : i < w) :
    x.abs[i] = if x.msb then (-x)[i] else x[i]
```

V variant:
```lean
@[grind =]
theorem getElemV_abs {i : Nat} {x : BitVec w} (h : i < w) :
    x.abs｢i｣ = if x.msb then (-x)｢i｣ else x｢i｣
```

### `Bitblast.lean`

#### 21. `getElem_add_add_bool` (line 287) — no annotation

Source signature:
```lean
theorem getElem_add_add_bool {i : Nat} (i_lt : i < w) (x y : BitVec w) (c : Bool) :
    (x + y + setWidth w (ofBool c))[i] =
      (x[i] ^^ (y[i] ^^ carry i x y c))
```

V variant:
```lean
theorem getElemV_add_add_bool {i : Nat} (i_lt : i < w) (x y : BitVec w) (c : Bool) :
    (x + y + setWidth w (ofBool c))｢i｣ =
      (x｢i｣ ^^ (y｢i｣ ^^ carry i x y c))
```

Note: `i_lt : i < w` needed because `carry` depends on bit values at indices < i.

#### 22. `getElem_add` (line 294) — no annotation

Source signature:
```lean
theorem getElem_add {i : Nat} (i_lt : i < w) (x y : BitVec w) :
    (x + y)[i] = (x[i] ^^ (y[i] ^^ carry i x y false))
```

V variant:
```lean
theorem getElemV_add {i : Nat} (i_lt : i < w) (x y : BitVec w) :
    (x + y)｢i｣ = (x｢i｣ ^^ (y｢i｣ ^^ carry i x y false))
```

#### 23. `getElem_sub` (line 371) — no annotation

Source signature:
```lean
theorem getElem_sub {i : Nat} {x y : BitVec w} (h : i < w) :
    (x - y)[i] = (x[i] ^^ ((~~~y + 1#w)[i] ^^ carry i x (~~~y + 1#w) false))
```

V variant:
```lean
theorem getElemV_sub {i : Nat} {x y : BitVec w} (h : i < w) :
    (x - y)｢i｣ = (x｢i｣ ^^ ((~~~y + 1#w)｢i｣ ^^ carry i x (~~~y + 1#w) false))
```

#### 24. `getElem_mul` (line 680) — no annotation

Source signature:
```lean
theorem getElem_mul {x y : BitVec w} {i : Nat} (h : i < w) :
    (x * y)[i] = (mulRec x y w)[i]
```

V variant:
```lean
theorem getElemV_mul {x y : BitVec w} {i : Nat} (h : i < w) :
    (x * y)｢i｣ = (mulRec x y w)｢i｣
```

#### 25. `getElem_udiv` (line 1133) — no annotation

Source signature:
```lean
theorem getElem_udiv (n d : BitVec w) (hy : 0#w < d) (i : Nat) (hi : i < w) :
    (n / d)[i] = (divRec w {n, d} (DivModState.init w)).q[i]
```

V variant:
```lean
theorem getElemV_udiv (n d : BitVec w) (hy : 0#w < d) (i : Nat) (hi : i < w) :
    (n / d)｢i｣ = (divRec w {n, d} (DivModState.init w)).q｢i｣
```

Note: `hy` is needed for the mathematical statement; `hi` is needed because
`divRec` result has width `w`.

#### 26. `getElem_umod` (line 1377) — no annotation

Source signature:
```lean
theorem getElem_umod {n d : BitVec w} (hi : i < w) :
    (n % d)[i]
      = if d = 0#w then n[i]
      else (divRec w { n := n, d := d } (DivModState.init w)).r[i]
```

V variant:
```lean
theorem getElemV_umod {n d : BitVec w} (hi : i < w) :
    (n % d)｢i｣
      = if d = 0#w then n｢i｣
      else (divRec w { n := n, d := d } (DivModState.init w)).r｢i｣
```

#### 27. `getElem_sdiv` (line 1689) — no annotation

Source signature:
```lean
theorem getElem_sdiv {x y : BitVec w} (h : i < w) :
    (x.sdiv y)[i] =
      (match x.msb, y.msb with
      | false, false => (x / y)[i]
      | false, true => (-(x / -y))[i]
      | true, false => (-(-x / y))[i]
      | true, true => (-x / -y)[i])
```

V variant:
```lean
theorem getElemV_sdiv {x y : BitVec w} (h : i < w) :
    (x.sdiv y)｢i｣ =
      match x.msb, y.msb with
      | false, false => (x / y)｢i｣
      | false, true => (-(x / -y))｢i｣
      | true, false => (-(-x / y))｢i｣
      | true, true => (-x / -y)｢i｣
```

#### 28. `getElem_srem` (line 1800) — no annotation

Source signature:
```lean
theorem getElem_srem {x y : BitVec w} (h : i < w) :
    (x.srem y)[i] =
      match x.msb, y.msb with
      | false, false => (x % y)[i]
      | false, true => (x % -y)[i]
      | true, false => (-(-x % y))[i]
      | true, true => (-(-x % -y))[i]
```

V variant:
```lean
theorem getElemV_srem {x y : BitVec w} (h : i < w) :
    (x.srem y)｢i｣ =
      match x.msb, y.msb with
      | false, false => (x % y)｢i｣
      | false, true => (x % -y)｢i｣
      | true, false => (-(-x % y))｢i｣
      | true, true => (-(-x % -y))｢i｣
```

#### 29. `getElem_smod` (line 2009) — no annotation

Source signature:
```lean
theorem getElem_smod {x y : BitVec w} (h : i < w) :
    (x.smod y)[i] =
      match x.msb, y.msb with
      | false, false => (x % y)[i]
      | false, true => (if x % -y = 0#w then (x % -y) else (x % -y + y))[i]
      | true, false => (if -x % y = 0#w then (-x % y) else (y - -x % y))[i]
      | true, true => (if -x % -y = 0#w then (-x % -y) else -(-x % -y + y))[i]
```

V variant:
```lean
theorem getElemV_smod {x y : BitVec w} (h : i < w) :
    (x.smod y)｢i｣ =
      match x.msb, y.msb with
      | false, false => (x % y)｢i｣
      | false, true => (if x % -y = 0#w then (x % -y) else (x % -y + y))｢i｣
      | true, false => (if -x % y = 0#w then (-x % y) else (y - -x % y))｢i｣
      | true, true => (if -x % -y = 0#w then (-x % -y) else -(-x % -y + y))｢i｣
```

### `Basic.lean`

#### 30. `getElem_eq_testBit_toNat` (line 128) — `@[grind =_]`

Source signature:
```lean
theorem getElem_eq_testBit_toNat (x : BitVec w) (i : Nat) (h : i < w) :
    x[i] = x.toNat.testBit i
```

V variant:
```lean
@[grind =_]
theorem getElemV_eq_testBit_toNat (x : BitVec w) (i : Nat) (h : i < w) :
    x｢i｣ = x.toNat.testBit i
```

Note: `h : i < w` needed because `testBit` is `false` for `i ≥ w` but
`getElemV` returns `Classical.ofNonempty`.

#### 31. `getLsbD_eq_getElem` (line 132) — `@[simp, grind =]`

Source signature:
```lean
theorem getLsbD_eq_getElem {x : BitVec w} {i : Nat} (h : i < w) :
    x.getLsbD i = x[i]
```

V variant:
```lean
@[simp, grind =]
theorem getLsbD_eq_getElemV {x : BitVec w} {i : Nat} (h : i < w) :
    x.getLsbD i = x｢i｣
```

Note: `h : i < w` needed because `getLsbD` returns `false` for out-of-bounds
but `getElemV` returns `Classical.ofNonempty`.

## Excluded candidates

### `getElem_eq_iff` (line 94)
This is a meta-lemma about the relationship between `getElem` and `getElem?`.
A V variant would be `getElemV_eq_iff` but it's not clear what the statement would
be since the proof `h` is embedded in the type. Skip — not a natural V variant candidate.

### `getElem_of_getLsbD_eq_true` (line 110)
Source: `(x[i]'(lt_of_getLsbD h) = true) = True`. This is a simplification lemma
that extracts a bound from `getLsbD`. The V variant would be trivial since `x｢i｣ = true`
follows from `getLsbD = true` via the bridge lemma. Not needed.

### `two_pow_le_toNat_of_getElem_eq_true` (line 142)
This is not a `getElem` *simplification* lemma but an *inference* lemma. The V variant
would be identical (replace `x[i]` with `x｢i｣` and add `h : i < w`). Low priority.

### `getElem_zero_ofNat_zero` (line 414)
Source: `(BitVec.ofNat w 0)[i] = false` with `h : i < w`.
V variant would need `h : i < w` (out-of-bounds is `Classical.ofNonempty ≠ false`).
Low value — covered by `getElemV_setWidth` + `simp`.

### `getElem_zero_ofNat_one` (line 417)
Source: `(BitVec.ofNat w 1)[0] = true` with `h : 0 < w`.
Same situation. Low priority.

### `getElem_eq_extractLsb'` (line 1254)
This converts `getElem` to `extractLsb'` — niche usage. Low priority.

### `getElem_rev` (line 3213)
Uses `Fin w` indexing: `x[i.rev]` where `i : Fin w`. The bound is provided by
`Fin.val_lt`. A V variant is not natural since `Fin` already carries the proof.
Skip.

### `getElem_eq_true_of_lt_of_le` (line 6073)
Inference lemma, not a simplification lemma. Low priority.

### `getElem_zero_ofBool` (line 437) — deprecated
Already deprecated. Skip.

## Summary

- **Prerequisite**: Add `GetElemV`/`LawfulGetElemV` instances + bridge lemma (Step 0)
- **31 candidates audited**, **31 V variants proposed** (numbered 1–31 above)
- **0 excluded** (2 earlier exclusions were re-evaluated as actionable)
- **Key pattern**: Most lemmas retain `h : i < w` because out-of-bounds `getElemV` returns
  `Classical.ofNonempty` which cannot be equated to concrete `Bool` values.
  The main benefit of V variants here is replacing `x[j]` on the RHS with `x｢j｣` to avoid
  needing to carry around sub-proofs of index bounds within the statement.
- **Estimated effort**: Medium — the instance + bridge lemma is the main new work;
  individual V variant proofs should mostly follow from `simp [getElemV_def]` + the original lemma.
