# Step 3e.4: BitVec V Lemma Parity (Full Audit)

Status: not started; Refinement Needed: no

## Files

`src/Init/Data/BitVec/Lemmas.lean`, `src/Init/Data/BitVec/Bootstrap.lean`,
`src/Init/Data/BitVec/Bitblast.lean`

## Context

Step 3a.5 created V variants for shift/rotate/arithmetic operations. This step covers the
remaining bitwise logic, constant, and structural operations.

## ACTIONABLE GAPS — V variants to create

### `Lemmas.lean` (~20 lemmas)

#### 1. `getElemV_zero` — `@[simp, grind =]`

Source signature:
```lean
@[simp, grind =] theorem getElem_zero (h : i < w) : (0#w)[i] = false
```

V variant:
```lean
@[simp, grind =]
theorem getElemV_zero (h : i < w) : (0#w)｢i｣ = false
```

Note: `h : i < w` retained — out-of-bounds returns `Classical.ofNonempty`, not `false`.

#### 2. `getElemV_one` — `@[simp, grind =]`

Source signature:
```lean
@[simp, grind =] theorem getElem_one (h : i < w) : (1#w)[i] = decide (i = 0)
```

V variant:
```lean
@[simp, grind =]
theorem getElemV_one (h : i < w) : (1#w)｢i｣ = decide (i = 0)
```

Note: `h : i < w` retained — RHS is a concrete Bool expression.

#### 3. `getElemV_ofFin` — `@[simp]`

Source signature:
```lean
@[simp] theorem getElem_ofFin (x : Fin (2^n)) (i : Nat) (h : i < n) :
    (BitVec.ofFin x)[i] = x.val.testBit i
```

V variant:
```lean
@[simp]
theorem getElemV_ofFin (x : Fin (2^n)) (i : Nat) (h : i < n) :
    (BitVec.ofFin x)｢i｣ = x.val.testBit i
```

Note: `h : i < n` retained — `testBit` returns `false` for out-of-bounds but
`getElemV` returns `Classical.ofNonempty`.

#### 4. `getElemV_cast` — `@[simp, grind =]`

Source signature:
```lean
@[simp, grind =] theorem getElem_cast (h : w = v) (x : BitVec w) (p : i < v) :
    (x.cast h)[i] = x[i]
```

V variant:
```lean
@[simp, grind =]
theorem getElemV_cast (h : w = v) (x : BitVec w) :
    (x.cast h)｢i｣ = x｢i｣
```

Note: `p : i < v` dropped — both sides return `Classical.ofNonempty` when out of bounds
(since `w = v`, both bitvecs have the same width). Inner `x[i]` becomes `x｢i｣`.

#### 5. `getElemV_allOnes` — `@[simp, grind =]`

Source signature:
```lean
@[simp, grind =] theorem getElem_allOnes (i : Nat) (h : i < v) :
    (allOnes v)[i] = true
```

V variant:
```lean
@[simp, grind =]
theorem getElemV_allOnes (i : Nat) (h : i < v) :
    (allOnes v)｢i｣ = true
```

Note: `h : i < v` retained — RHS is `true`, not `Classical.ofNonempty`.

#### 6. `getElemV_or` — `@[simp, grind =]`

Source signature:
```lean
@[simp, grind =] theorem getElem_or {x y : BitVec w} {i : Nat} (h : i < w) :
    (x ||| y)[i] = (x[i] || y[i])
```

V variant:
```lean
@[simp, grind =]
theorem getElemV_or {x y : BitVec w} {i : Nat} (h : i < w) :
    (x ||| y)｢i｣ = (x｢i｣ || y｢i｣)
```

Note: `h : i < w` retained — RHS is a concrete Bool expression. Inner `x[i]`, `y[i]` become
`x｢i｣`, `y｢i｣`.

#### 7. `getElemV_and` — `@[simp, grind =]`

Source signature:
```lean
@[simp, grind =] theorem getElem_and {x y : BitVec w} {i : Nat} (h : i < w) :
    (x &&& y)[i] = (x[i] && y[i])
```

V variant:
```lean
@[simp, grind =]
theorem getElemV_and {x y : BitVec w} {i : Nat} (h : i < w) :
    (x &&& y)｢i｣ = (x｢i｣ && y｢i｣)
```

Note: `h : i < w` retained. Inner `x[i]`, `y[i]` become `x｢i｣`, `y｢i｣`.

#### 8. `getElemV_xor` — `@[simp, grind =]`

Source signature:
```lean
@[simp, grind =] theorem getElem_xor {x y : BitVec w} {i : Nat} (h : i < w) :
    (x ^^^ y)[i] = (x[i] ^^ y[i])
```

V variant:
```lean
@[simp, grind =]
theorem getElemV_xor {x y : BitVec w} {i : Nat} (h : i < w) :
    (x ^^^ y)｢i｣ = (x｢i｣ ^^ y｢i｣)
```

Note: `h : i < w` retained. Inner `x[i]`, `y[i]` become `x｢i｣`, `y｢i｣`.

#### 9. `getElemV_not` — `@[simp, grind =]`

Source signature:
```lean
@[simp, grind =] theorem getElem_not {x : BitVec w} {i : Nat} (h : i < w) :
    (~~~x)[i] = !x[i]
```

V variant:
```lean
@[simp, grind =]
theorem getElemV_not {x : BitVec w} {i : Nat} (h : i < w) :
    (~~~x)｢i｣ = !x｢i｣
```

Note: `h : i < w` retained. Inner `x[i]` becomes `x｢i｣`.

#### 10. `getElemV_ushiftRight` — `@[simp, grind =]`

Source signature:
```lean
@[simp, grind =] theorem getElem_ushiftRight (x : BitVec w) (i n : Nat) (h : i < w) :
    (x >>> n)[i] = x.getLsbD (n + i)
```

V variant:
```lean
@[simp, grind =]
theorem getElemV_ushiftRight (x : BitVec w) (i n : Nat) (h : i < w) :
    (x >>> n)｢i｣ = x.getLsbD (n + i)
```

Note: `h : i < w` retained — RHS uses `getLsbD` which returns `false` for out-of-bounds,
but LHS `getElemV` returns `Classical.ofNonempty`.

#### 11. `getElemV_extractLsb'` — `@[simp, grind =]`

Source signature:
```lean
@[simp, grind =] theorem getElem_extractLsb' {start len : Nat} {x : BitVec n} {i : Nat}
    (h : i < len) :
    (extractLsb' start len x)[i] = x.getLsbD (start+i)
```

V variant:
```lean
@[simp, grind =]
theorem getElemV_extractLsb' {start len : Nat} {x : BitVec n} {i : Nat} (h : i < len) :
    (extractLsb' start len x)｢i｣ = x.getLsbD (start + i)
```

Note: `h : i < len` retained — `extractLsb'` produces a `BitVec len`, and the RHS
uses `getLsbD` which differs from `Classical.ofNonempty` out of bounds.

#### 12. `getElemV_extract` — `@[simp, grind =]`

Source signature:
```lean
@[simp, grind =] theorem getElem_extract {hi lo : Nat} {x : BitVec n} {i : Nat}
    (h : i < hi - lo + 1) :
    (extractLsb hi lo x)[i] = getLsbD x (lo+i)
```

V variant:
```lean
@[simp, grind =]
theorem getElemV_extract {hi lo : Nat} {x : BitVec n} {i : Nat} (h : i < hi - lo + 1) :
    (extractLsb hi lo x)｢i｣ = getLsbD x (lo + i)
```

Note: `h : i < hi - lo + 1` retained — `extractLsb` produces a `BitVec (hi - lo + 1)`.

#### 13. `getElemV_shiftLeftZeroExtend` — `@[simp]`

Source signature:
```lean
@[simp] theorem getElem_shiftLeftZeroExtend {x : BitVec m} {n : Nat} (h : i < m + n) :
    (shiftLeftZeroExtend x n)[i] = if h' : i < n then false else x[i - n]
```

V variant:
```lean
@[simp]
theorem getElemV_shiftLeftZeroExtend {x : BitVec m} {n : Nat} (h : i < m + n) :
    (shiftLeftZeroExtend x n)｢i｣ = if i < n then false else x｢i - n｣
```

Note: `h : i < m + n` retained — when `i ≥ n`, the RHS references `x｢i - n｣` which
needs `i - n < m` for a meaningful result. The `dif` becomes a plain `if`; inner
`x[i - n]` becomes `x｢i - n｣`.

#### 14. `getElemV_concat_zero` — `@[simp]`

Source signature:
```lean
@[simp] theorem getElem_concat_zero {x : BitVec w} : (concat x b)[0] = b
```

V variant:
```lean
@[simp]
theorem getElemV_concat_zero {x : BitVec w} : (concat x b)｢0｣ = b
```

Note: No `h` needed — `concat x b` has width `w + 1`, so `0 < w + 1` always holds.
The `getElemV` is always in-bounds.

#### 15. `getElemV_concat_succ` — `@[simp]`

Source signature:
```lean
@[simp] theorem getElem_concat_succ {x : BitVec w} {i : Nat} (h : i + 1 < w + 1) :
    (concat x b)[i + 1] = x[i]
```

V variant:
```lean
@[simp]
theorem getElemV_concat_succ {x : BitVec w} {i : Nat} (h : i + 1 < w + 1) :
    (concat x b)｢i + 1｣ = x｢i｣
```

Note: `h : i + 1 < w + 1` retained (equivalently `i < w`) — both sides need in-bounds
for meaningful equality. Inner `x[i]` becomes `x｢i｣`.

#### 16. `getElemV_ofBoolListBE` — `@[simp, grind =]`

Source signature:
```lean
@[simp, grind =] theorem getElem_ofBoolListBE (h : i < bs.length) :
    (ofBoolListBE bs)[i] = bs[bs.length - 1 - i]
```

V variant:
```lean
@[simp, grind =]
theorem getElemV_ofBoolListBE (h : i < bs.length) :
    (ofBoolListBE bs)｢i｣ = bs[bs.length - 1 - i]
```

Note: `h : i < bs.length` retained — needed for the RHS `bs[bs.length - 1 - i]` to be
well-typed (list indexing requires a bound proof). `ofBoolListBE bs` has width `bs.length`.

#### 17. `getElemV_zero_ofNat_zero` — no annotation

Source signature:
```lean
theorem getElem_zero_ofNat_zero (i : Nat) (h : i < w) :
    (BitVec.ofNat w 0)[i] = false
```

V variant:
```lean
theorem getElemV_zero_ofNat_zero (i : Nat) (h : i < w) :
    (BitVec.ofNat w 0)｢i｣ = false
```

Note: `h : i < w` retained — RHS is `false`, not `Classical.ofNonempty`.

#### 18. `getElemV_zero_ofNat_one` — no annotation

Source signature:
```lean
theorem getElem_zero_ofNat_one (h : 0 < w) : (BitVec.ofNat w 1)[0] = true
```

V variant:
```lean
theorem getElemV_zero_ofNat_one (h : 0 < w) : (BitVec.ofNat w 1)｢0｣ = true
```

Note: `h : 0 < w` retained — RHS is `true`, not `Classical.ofNonempty`.

#### 19. `getElemV_rev` — `@[grind =]`

Source signature:
```lean
@[grind =] theorem getElem_rev {x : BitVec w} {i : Fin w} :
    x[i.rev] = x.getMsbD i
```

V variant:
```lean
@[grind =]
theorem getElemV_rev {x : BitVec w} {i : Nat} (h : i < w) :
    x｢w - 1 - i｣ = x.getMsbD i
```

Note: The original uses `Fin w` and `i.rev` (= `w - 1 - i`). The V variant uses `Nat`
indexing with `h : i < w` retained — needed so `w - 1 - i < w` and `getMsbD` gives
the expected result.

#### 20. `getElemV_reverse` — `@[grind =]`

Source signature:
```lean
@[grind =] theorem getElem_reverse (x : BitVec w) (h : i < w) :
    x.reverse[i] = x.getMsbD i
```

V variant:
```lean
@[grind =]
theorem getElemV_reverse (x : BitVec w) (h : i < w) :
    x.reverse｢i｣ = x.getMsbD i
```

Note: `h : i < w` retained — `getMsbD` returns `false` for out-of-bounds but
`getElemV` returns `Classical.ofNonempty`.

### `Bootstrap.lean` (1 lemma)

#### 21. `getElemV_cons` — `@[grind =]`

Source signature:
```lean
theorem getElem_cons {b : Bool} {n} {x : BitVec n} {i : Nat} (h : i < n + 1) :
    (cons b x)[i] = if h : i = n then b else x[i]
```

V variant:
```lean
@[grind =]
theorem getElemV_cons {b : Bool} {n} {x : BitVec n} {i : Nat} (h : i < n + 1) :
    (cons b x)｢i｣ = if i = n then b else x｢i｣
```

Note: `h : i < n + 1` retained — `cons b x` has width `n + 1`, and the RHS depends on
whether `i = n`. The `dif` becomes a plain `if`; inner `x[i]` becomes `x｢i｣`.

### `Bitblast.lean` (1 lemma)

#### 22. `getElemV_neg` — no annotation

Source signature:
```lean
theorem getElem_neg {i : Nat} {x : BitVec w} (h : i < w) :
    (-x)[i] = (x[i] ^^ decide (∃ j < i, x.getLsbD j = true))
```

V variant:
```lean
theorem getElemV_neg {i : Nat} {x : BitVec w} (h : i < w) :
    (-x)｢i｣ = (x｢i｣ ^^ decide (∃ j < i, x.getLsbD j = true))
```

Note: `h : i < w` retained — needed for the carry computation to be meaningful.
Inner `x[i]` becomes `x｢i｣`. The `getLsbD` references on the RHS remain as-is since
they are already total.

## Notes

- Most of these retain `h : i < w` because out-of-bounds `getElemV` returns
  `Classical.ofNonempty` which can't be equated to specific Bool values.
- The main benefit of V variants is replacing RHS occurrences of `x[j]` with `x｢j｣`,
  eliminating the need to carry sub-proofs of index bounds within the statement.
- Exception: `getElemV_cast` (#4) can drop its bound `p : i < v` entirely, since both
  sides refer to the same-width bitvec and return `Classical.ofNonempty` in tandem.
- Exception: `getElemV_concat_zero` (#14) needs no bound since `0 < w + 1` is always true.
- `getElemV_rev` (#19) translates from `Fin`-based to `Nat`-based indexing.
- Proofs: `simp [getElemV_pos h]` for most; some may need `simp [getElemV_eq_getLsbD]`.

## Total: 22 new V variant lemmas
