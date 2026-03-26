# Step 3e.2: List V Lemma Parity (Full Audit)

Status: not started; Refinement Needed: no

## Files

Multiple files under `src/Init/Data/List/`.

## Goal

Add V variants for ALL remaining proof-taking lemmas in List. This is the largest sub-step,
covering getElem V variants (~55 lemmas) and head/getLast V variants (~48 lemmas).

## Part A: getElem V variants (~55 lemmas)

### `OfFn.lean` (1)

| V lemma | Counterpart | Annotation |
|---------|-------------|------------|
| `ofFn_getElemV` | `ofFn_getElem` (line 115) | `@[simp]` |

#### Suggested signatures

```lean
-- ofFn_getElem uses Fin-based indexing internally; V variant replaces l[i.val] with l｢i.val｣
@[simp]
theorem ofFn_getElemV {_ : Nonempty α} {xs : List α} :
    List.ofFn (fun i : Fin xs.length => xs｢i.val｣) = xs
```

### `FinRange.lean` (1)

| V lemma | Counterpart | Annotation |
|---------|-------------|------------|
| `getElemV_finRange` | `getElem_finRange` (line 33) | none |

#### Suggested signatures

```lean
-- getElem_finRange : (finRange n)[i] = Fin.cast length_finRange ⟨i, h⟩
-- The V variant keeps the bound because the RHS produces a specific Fin value.
theorem getElemV_finRange {i : Nat} (h : i < (List.finRange n).length) :
    (finRange n)｢i｣ = Fin.cast length_finRange ⟨i, h⟩
```

### `Lemmas.lean` (~25)

| V lemma | Counterpart | Annotation | Status |
|---------|-------------|------------|--------|
| `getElemV_eq_iff` | `getElem_eq_iff` | none | create |
| `getElemV_of_eq` | `getElem_of_eq` | none | create |
| `getElemV_zero` | `getElem_zero` (line 329) | none | EXISTS as `getElemV_zero_eq_headV` |
| `getElemV_cons` | `getElem_cons` (line 239) | none | EXISTS (line 233) |
| `getElemV_cons_length` | `getElem_cons_length` | none | EXISTS (line 1088) |
| `getElemV_concat_length` | `getElem_concat_length` (line 376) | none | EXISTS (line 372) |
| `eq_getElemV_of_length_eq_one` | `eq_getElem_of_length_eq_one` | none | create |
| `eq_getElemV_of_length_eq_two` | `eq_getElem_of_length_eq_two` | none | create |
| `eq_getElemV_of_length_eq_three` | `eq_getElem_of_length_eq_three` | none | create |
| `eq_getElemV_of_length_eq_four` | `eq_getElem_of_length_eq_four` | none | create |
| `getElemV_of_mem` | `getElem_of_mem` (line 531) | none | EXISTS (line 525) |
| `mem_of_getElemV` | `mem_of_getElem` | none | EXISTS (line 539) |
| `mem_iff_getElemV` | `mem_iff_getElem` | none | EXISTS (line 550) |
| `getElemV_eq_getD` | `getElem_eq_getD` | none | create |
| `getD_getElemV` | `getD_getElem` (line 288) | none | EXISTS as `getD_getElem?_eq_getElemV` (line 296) |
| `getElemV_append` | `getElem_append` (line 1907) | none | EXISTS (line 1913) |
| `getElemV_append_left` | `getElem_append_left` (line 1954) | none | EXISTS as `getElemV_append_left'` (line 1939) |
| `getElemV_append_right` | `getElem_append_right` (line 1959) | none | EXISTS as `getElemV_append_right'` (line 1945) |
| `getElemV_of_append` | `getElem_of_append` (line 1963) | none | EXISTS (line 1949) |
| `getElemV_reverse` | `getElem_reverse` (line 2808) | none | EXISTS (line 2800) |
| `getElemV_filter` | `getElem_filter` | none | EXISTS (line 1601) |
| `getElemV_dropLast` | `getElem_dropLast` (line 3570) | none | EXISTS (line 3560) |
| `getElemV_replace_of_ne` | `getElem_replace_of_ne` (line 3900) | none | EXISTS (line 3890) |
| `ext_getElemV_iff` | `ext_getElem_iff` (line 366) | none | EXISTS (line 351) |

#### Suggested signatures (for lemmas that need to be created)

```lean
-- getElem_eq_iff : l[i] = x ↔ l[i]? = some x  (proof h : i < l.length)
-- V variant: keep the bound since out-of-bounds makes the iff trivially wrong.
theorem getElemV_eq_iff {l : List α} {i : Nat} (h : i < l.length) :
    l｢i｣ = x ↔ l[i]? = some x

-- getElem_of_eq : l[i] = l'[i]'(h ▸ w) given h : l = l'
-- V variant: trivially follows from congr, but included for completeness.
theorem getElemV_of_eq {_ : Nonempty α} {l l' : List α} (h : l = l') {i : Nat} :
    l｢i｣ = l'｢i｣

-- eq_getElem_of_length_eq_one : l = [l[0]'...] when l.length = 1
-- V variant: replaces proof-taking getElem with getElemV
theorem eq_getElemV_of_length_eq_one (l : List α) (hl : l.length = 1) :
    l = [l｢0｣]

theorem eq_getElemV_of_length_eq_two (l : List α) (hl : l.length = 2) :
    l = [l｢0｣, l｢1｣]

theorem eq_getElemV_of_length_eq_three (l : List α) (hl : l.length = 3) :
    l = [l｢0｣, l｢1｣, l｢2｣]

theorem eq_getElemV_of_length_eq_four (l : List α) (hl : l.length = 4) :
    l = [l｢0｣, l｢1｣, l｢2｣, l｢3｣]

-- getElem_eq_getD : l[i] = l.getD i fallback  (proof h : i < l.length)
-- V variant: the bound is needed so both sides agree.
theorem getElemV_eq_getD {l : List α} {i : Nat} (h : i < l.length) (fallback : α) :
    l｢i｣ = l.getD i fallback
```

### `Nat/Basic.lean` (4)

| V lemma | Counterpart | Annotation | Status |
|---------|-------------|------------|--------|
| `getElemV_eq_getElemV_reverse` | `getElem_eq_getElem_reverse` (line 95) | none | create |
| `getElemV_intersperse_two_mul` | `getElem_intersperse_two_mul` (line 160) | none | EXISTS (line 165) |
| `getElemV_eq_getElemV_intersperse_two_mul` | `getElem_eq_getElem_intersperse_two_mul` (line 201) | none | create |
| `mem_eraseIdx_iff_getElemV` | `mem_eraseIdx_iff_getElem` (line 209) | none | create |

#### Suggested signatures

```lean
-- getElem_eq_getElem_reverse : l[i] = l.reverse[l.length - 1 - i]'(...)
-- V variant: keep the bound since the equation is only meaningful in-bounds.
theorem getElemV_eq_getElemV_reverse {l : List α} {i} (h : i < l.length) :
    haveI : Nonempty α := ⟨l[i]⟩
    l｢i｣ = l.reverse｢l.length - 1 - i｣

-- getElem_eq_getElem_intersperse_two_mul : l[i] = (l.intersperse sep)[2 * i]'(...)
-- V variant: keep the bound for meaningfulness.
theorem getElemV_eq_getElemV_intersperse_two_mul {l : List α} {sep : α} {i : Nat}
    (h : i < l.length) :
    haveI : Nonempty α := ⟨sep⟩
    l｢i｣ = (l.intersperse sep)｢2 * i｣

-- mem_eraseIdx_iff_getElem : x ∈ eraseIdx l k ↔ ∃ i h, i ≠ k ∧ l[i]'h = x
-- The bound h is essential for the characterization. NOT APPLICABLE for V form.
-- Keeping for reference; may skip if deemed not useful.
theorem mem_eraseIdx_iff_getElemV {x : α} {l : List α} {k : Nat} :
    x ∈ eraseIdx l k ↔ ∃ i, ∃ _ : i < l.length, i ≠ k ∧ l｢i｣ = x
```

### `Nat/Modify.lean` (6)

| V lemma | Counterpart | Annotation | Status |
|---------|-------------|------------|--------|
| `getElemV_modifyHead` | `getElem_modifyHead` (line 43) | `@[grind =]` | create |
| `getElemV_modifyHead_zero` | `getElem_modifyHead_zero` (line 49) | none | EXISTS (line 52) |
| `getElemV_modifyHead_succ` | `getElem_modifyHead_succ` (line 57) | none | EXISTS (line 60) |
| `getElemV_modify` | `getElem_modify` (line 217) | none | EXISTS (line 224) |
| `getElemV_modify_eq` | `getElem_modify_eq` (line 240) | none | EXISTS (line 243) |
| `getElemV_modify_ne` | `getElem_modify_ne` (line 248) | none | EXISTS (line 251) |

#### Suggested signatures (for lemmas that need to be created)

```lean
-- getElem_modifyHead has an if/then/else on i = 0. The combined V variant:
@[grind =]
theorem getElemV_modifyHead {_ : Nonempty α} {l : List α} {f : α → α} {i : Nat} :
    (l.modifyHead f)｢i｣ = if i = 0 ∧ 0 < l.length then f l｢0｣ else l｢i｣
```

### `Nat/BEq.lean` (2)

| V lemma | Counterpart | Annotation |
|---------|-------------|------------|
| V-form of `isEqv_eq_decide` | line 22 | none |
| V-form of `beq_eq_decide` | line 50 | none |

#### Suggested signatures

```lean
-- isEqv_eq_decide: ∀ i (h' : i < as.length), r (as[i]'...) (bs[i]'...)
-- V variant keeps the bound, replaces as[i]'/bs[i]' with as｢i｣/bs｢i｣.
theorem isEqv_eq_decideV {_ : Nonempty α} {as bs : List α} {r : α → α → Bool} :
    isEqv as bs r = if as.length = bs.length then
      decide (∀ (i : Nat), i < as.length → r as｢i｣ bs｢i｣) else false

theorem beq_eq_decideV {_ : Nonempty α} [BEq α] {as bs : List α} :
    (as == bs) = if as.length = bs.length then
      decide (∀ (i : Nat), i < as.length → as｢i｣ == bs｢i｣) else false
```

### `Nat/Sublist.lean` (1)

| V lemma | Counterpart | Annotation |
|---------|-------------|------------|
| V-form of `suffix_iff_getElem` | line 70 | none |

#### Suggested signatures

```lean
-- suffix_iff_getElem: ∀ i (_ : i < l₁.length), l₂[i + l₂.length - l₁.length] = l₁[i]
-- V variant keeps bounds, replaces l₁[i]/l₂[...] with l₁｢i｣/l₂｢...｣.
theorem suffix_iff_getElemV [Nonempty α] {l₁ l₂ : List α} :
    l₁ <:+ l₂ ↔ ∃ (_ : l₁.length ≤ l₂.length),
      ∀ i, i < l₁.length → l₂｢i + l₂.length - l₁.length｣ = l₁｢i｣
```

### `Nat/TakeDrop.lean` (3)

| V lemma | Counterpart | Annotation | Status |
|---------|-------------|------------|--------|
| `getElemV_take` | `getElem_take` (line 53) | none | create |
| `getElemV_drop` | `getElem_drop` (line 237) | none | create |
| `getElemV_zipWith` | `getElem_zipWith` (line 600) | `@[simp, grind =]` | create |

#### Suggested signatures

```lean
-- getElem_take : (xs.take j)[i] = xs[i]'(...)  (proof h : i < (xs.take j).length)
-- V variant: out-of-bounds on both sides returns garbage consistently.
@[simp, grind =]
theorem getElemV_take {_ : Nonempty α} {xs : List α} {j i : Nat} :
    (xs.take j)｢i｣ = xs｢i｣

-- getElem_drop : (xs.drop i)[j] = xs[i + j]'(...)
-- V variant: out-of-bounds returns garbage consistently.
@[simp, grind =]
theorem getElemV_drop {_ : Nonempty α} {xs : List α} {i j : Nat} :
    (xs.drop i)｢j｣ = xs｢i + j｣

-- getElem_zipWith : (zipWith f l l')[i] = f l[i] l'[i]
-- The bound is essential because f applied to garbage inputs may differ from
-- Classical.ofNonempty γ. Keep the bound.
@[simp, grind =]
theorem getElemV_zipWith {f : α → β → γ} {l : List α} {l' : List β}
    {i : Nat} (h : i < (zipWith f l l').length) :
    haveI : Nonempty γ := ⟨f (l[i]'(lt_length_left_of_zipWith h)) (l'[i]'(lt_length_right_of_zipWith h))⟩
    (zipWith f l l')｢i｣ = f l｢i｣ l'｢i｣
```

### Other files (8)

| V lemma | File | Counterpart | Annotation | Status |
|---------|------|-------------|------------|--------|
| V-form of `lex_eq_true_iff_exists` | Lex.lean | line 367 | none | create |
| V-form of `lex_eq_false_iff_exists` | Lex.lean | line 428 | none | create |
| `boole_getElemV_le_countP` | Count.lean | line 129 | none | create |
| `boole_getElemV_le_count` | Count.lean | line 319 | none | create |
| `getElemV_zipIdx` | Range.lean | line 233 | `@[simp, grind =]` | create |
| V-form of `prefix_iff_getElem` | Sublist.lean | line 990 | none | create |
| `getElemV_succ_scanl` | Scan/Lemmas.lean | line 220 | none | create |
| `findIdx_getElemV` + variants | Find.lean | lines 588-670 | none | create (partial) |

#### Suggested signatures

```lean
-- lex_eq_true_iff_exists: contains l₁[j]'... == l₂[j]'... and lt l₁[i] l₂[i]
-- V variant keeps all bounds, replaces proof-taking indexing with ｢·｣.
theorem lex_eq_true_iff_existsV [Nonempty α] [BEq α] {lt : α → α → Bool}
    {l₁ l₂ : List α} :
    lex l₁ l₂ lt = true ↔
      (l₁.isEqv (l₂.take l₁.length) (· == ·) ∧ l₁.length < l₂.length) ∨
        (∃ (i : Nat) (_ : i < l₁.length) (_ : i < l₂.length),
          (∀ j, j < i → l₁｢j｣ == l₂｢j｣) ∧ lt l₁｢i｣ l₂｢i｣)

-- lex_eq_false_iff_exists: same pattern
-- (signature to be derived from source at implementation time — complex statement)

-- prefix_iff_getElem: ∀ i (hx : i < l₁.length), l₁[i] = l₂[i]'(...)
-- V variant keeps bounds, replaces l₁[i]/l₂[i]' with l₁｢i｣/l₂｢i｣.
theorem prefix_iff_getElemV [Nonempty α] {l₁ l₂ : List α} :
    l₁ <+: l₂ ↔ ∃ (_ : l₁.length ≤ l₂.length),
      ∀ i, i < l₁.length → l₁｢i｣ = l₂｢i｣

-- boole_getElem_le_countP : (if p l[i] then 1 else 0) ≤ l.countP p
-- The bound h : i < l.length is needed; out-of-bounds makes the inequality vacuously
-- true with garbage in the condition. Keep bound.
theorem boole_getElemV_le_countP {p : α → Bool} {l : List α} {i : Nat} (h : i < l.length) :
    (if p l｢i｣ then 1 else 0) ≤ l.countP p

theorem boole_getElemV_le_count [BEq α] {a : α} {l : List α} {i : Nat} (h : i < l.length) :
    (if l｢i｣ == a then 1 else 0) ≤ l.count a

-- getElem_zipIdx : (l.zipIdx j)[i] = (l[i]'(...), j + i)
-- The result is a pair (α × Nat). Keep bound because Classical.ofNonempty (α × Nat)
-- may differ from (Classical.ofNonempty α, ...).
@[simp, grind =]
theorem getElemV_zipIdx {l : List α} {i j : Nat} (h : i < (l.zipIdx j).length) :
    haveI : Nonempty (α × Nat) := ⟨(l[i]'(by simpa [length_zipIdx] using h), j + i)⟩
    (l.zipIdx j)｢i｣ = (l｢i｣, j + i)

-- getElem_succ_scanl : (scanl f b l)[i+1] = f (scanl f b l)[i] l[i]
-- Bounds are needed since f applied to garbage may differ from Classical.ofNonempty.
theorem getElemV_succ_scanl {f : β → α → β} (h : i + 1 < (scanl f b l).length) :
    haveI : Nonempty β := ⟨b⟩
    (scanl f b l)｢i + 1｣ = f (l.scanl f b)｢i｣ l｢i｣

-- findIdx_getElem: p xs[xs.findIdx p] with w : xs.findIdx p < xs.length
-- V variant keeps w, replaces xs[xs.findIdx p] with xs｢xs.findIdx p｣.
theorem findIdx_getElemV {p : α → Bool} {xs : List α}
    (w : xs.findIdx p < xs.length) :
    p xs｢xs.findIdx p｣

-- not_of_lt_findIdx: p (xs[i]'(...)) = false given h : i < xs.findIdx p
-- V variant keeps h, replaces xs[i]'proof with xs｢i｣.
theorem not_of_lt_findIdxV {_ : Nonempty α} {p : α → Bool} {xs : List α} {i : Nat}
    (h : i < xs.findIdx p) :
    p xs｢i｣ = false

-- findIdx_eq: xs.findIdx p = i ↔ p xs[i] ∧ ∀ j (hji : j < i), p (xs[j]'...) = false
-- V variant keeps h, replaces all xs[·]'proof with xs｢·｣.
theorem findIdxV_eq {p : α → Bool} {xs : List α} {i : Nat}
    (h : i < xs.length) :
    haveI : Nonempty α := ⟨xs[i]'h⟩
    xs.findIdx p = i ↔ p xs｢i｣ ∧ ∀ j, j < i → p xs｢j｣ = false
```

## Part B: head/getLast V variants (~48 lemmas)

### `Lemmas.lean` (~25)

| V lemma | Counterpart | Annotation | Status |
|---------|-------------|------------|--------|
| `headV_map` | `head_map` (line 1485) | `@[simp]` | EXISTS (line 1491) |
| `headV_filter_of_pos` | `head_filter_of_pos` (line 1685) | none | EXISTS (line 1693) |
| `headV_filterMap_of_eq_some` | `head_filterMap_of_eq_some` (line 1813) | none | EXISTS (line 1822) |
| `headV_append_of_ne_nil` | `head_append_of_ne_nil` (line 2069) | none | EXISTS (line 2063) |
| `headV_append` | `head_append` (line 2092) | `@[grind =]` | EXISTS (line 2074) |
| `headV_append_left` | `head_append_left` (line 2100) | none | EXISTS (line 2083) |
| `headV_append_right` | `head_append_right` (line 2104) | none | EXISTS (line 2088) |
| `headV_replicate` | `head_replicate` (line 2573) | `@[simp]` | EXISTS (line 2566) |
| `headV_reverse` | `head_reverse` (line 3298) | `@[simp, grind =]` | EXISTS (line 3283) |
| `headV_dropLast` | `head_dropLast` (line 3591) | none | EXISTS (line 3581) |
| `headV_replace` | `head_replace` (line 3926) | none | EXISTS (line 3914) |
| `headV_insert` | `head_insert` (line 4088) | none | EXISTS (line 4083) |
| `headV_tail` | `head_tail` (line 1302) | `@[simp]` | EXISTS (line 1308) |
| `cons_headV_tail` | `cons_head_tail` (line 1335) | `@[simp, grind =]` | EXISTS (line 1340) |
| `getLastV_map` | `getLast_map` (line 1512) | `@[simp]` | EXISTS (line 1522) |
| `getLastV_concat` | `getLast_concat` (line 2020) | none | EXISTS (line 2012) |
| `getLastV_append_of_ne_nil` | `getLast_append_of_ne_nil` (line 3367) | `@[simp]` | EXISTS (line 3328) |
| `getLastV_append` | `getLast_append` (line 3372) | `@[grind =]` | EXISTS (line 3335) |
| `getLastV_append_right` | `getLast_append_right` (line 3385) | none | EXISTS (line 3349) |
| `getLastV_append_left` | `getLast_append_left` (line 3389) | none | EXISTS (line 3354) |
| `getLastV_reverse` | `getLast_reverse` (line 3359) | `@[simp, grind =]` | EXISTS (line 3319) |
| `getLastV_replicate` | `getLast_replicate` (line 3438) | `@[simp]` | EXISTS (line 3433) |
| `getLastV_dropLast` | `getLast_dropLast` (line 3617) | none | EXISTS (line 3603) |
| `getLastV_tail` | `getLast_tail` (line 1314) | `@[simp, grind =]` | EXISTS (line 1321) |
| `headV_eq_getLastV_reverse` | `head_eq_getLast_reverse` (line 3363) | none | EXISTS (line 3323) |
| `getLastV_eq_headV_reverse` | `getLast_eq_head_reverse` (line 3302) | none | EXISTS (line 3294) |

All Part B `Lemmas.lean` entries already exist. Signatures are provided below for reference:

#### Existing signatures (for reference / annotation audit)

```lean
@[simp] theorem headV_map {f : α → β} {l : List α} (h : l ≠ []) :
    haveI : Nonempty β := ⟨f (l.head h)⟩
    (map f l).headV = f l.headV

theorem headV_filter_of_pos {_ : Nonempty α} {p : α → Bool} {l : List α}
    (h : p l.headV) :
    (filter p l).headV = l.headV

theorem headV_filterMap_of_eq_some {f : α → Option β} {l : List α} (w : l ≠ []) {b : β}
    (h : f (l.head w) = some b) :
    haveI : Nonempty β := ⟨b⟩
    (filterMap f l).headV = b

theorem headV_append_of_ne_nil {l : List α} (h : l ≠ []) :
    haveI : Nonempty α := ⟨l.head h⟩
    (l ++ l').headV = l.headV

@[grind =] theorem headV_append {_ : Nonempty α} {l₁ l₂ : List α} :
    (l₁ ++ l₂).headV = if l₁.isEmpty then l₂.headV else l₁.headV

theorem headV_append_left {l₁ l₂ : List α} (h : l₁ ≠ []) :
    haveI : Nonempty α := ⟨l₁.head h⟩
    (l₁ ++ l₂).headV = l₁.headV

theorem headV_append_right {_ : Nonempty α} {l₁ l₂ : List α} (h : l₁ = []) :
    (l₁ ++ l₂).headV = l₂.headV

@[simp] theorem headV_replicate (w : 0 < n) :
    haveI : Nonempty α := ⟨a⟩
    (replicate n a).headV = a

@[simp, grind =] theorem headV_reverse {_ : Nonempty α} {l : List α} :
    l.reverse.headV = l.getLastV

theorem headV_dropLast {xs : List α} (h : xs.dropLast ≠ []) :
    haveI : Nonempty α := ⟨xs.dropLast.head h⟩
    xs.dropLast.headV = xs.headV

theorem headV_replace {l : List α} {a b : α} (w : l ≠ []) :
    haveI : Nonempty α := ⟨l.head w⟩
    (l.replace a b).headV = if a == l.headV then b else l.headV

theorem headV_insert {l : List α} {a : α} :
    haveI : Nonempty α := ⟨a⟩
    (l.insert a).headV = if a ∈ l then l.headV else a

@[simp] theorem headV_tail {_ : Nonempty α} {l : List α} :
    (tail l).headV = l｢1｣

@[simp, grind =] theorem cons_headV_tail {l : List α} (h : l ≠ []) :
    haveI : Nonempty α := ⟨l.head h⟩
    l.headV :: l.tail = l

@[simp] theorem getLastV_map {f : α → β} {l : List α} (h : l ≠ []) :
    haveI : Nonempty β := ⟨f (l.head h)⟩
    (map f l).getLastV = f l.getLastV

theorem getLastV_concat {a : α} {l : List α} :
    haveI : Nonempty α := ⟨a⟩
    getLastV (l ++ [a]) = a

@[simp] theorem getLastV_append_of_ne_nil {l : List α} (h : l' ≠ []) :
    haveI : Nonempty α := ⟨l'.head h⟩
    (l ++ l').getLastV = l'.getLastV

@[grind =] theorem getLastV_append {_ : Nonempty α} {l : List α} :
    (l ++ l').getLastV = if l'.isEmpty then l.getLastV else l'.getLastV

theorem getLastV_append_right {l : List α} (h : l' ≠ []) :
    haveI : Nonempty α := ⟨l'.head h⟩
    (l ++ l').getLastV = l'.getLastV

theorem getLastV_append_left {l : List α} (w : l ++ l' ≠ []) (h : l' = []) :
    haveI : Nonempty α := ⟨head _ w⟩
    (l ++ l').getLastV = l.getLastV

@[simp, grind =] theorem getLastV_reverse {_ : Nonempty α} {l : List α} :
    l.reverse.getLastV = l.headV

@[simp] theorem getLastV_replicate (w : 0 < n) :
    haveI : Nonempty α := ⟨a⟩
    (replicate n a).getLastV = a

theorem getLastV_dropLast {xs : List α} (h : xs.dropLast ≠ []) :
    haveI : Nonempty α := ⟨xs.dropLast.head h⟩
    xs.dropLast.getLastV = xs｢xs.length - 2｣

@[simp, grind =] theorem getLastV_tail {l : List α} (h : l.tail ≠ []) :
    haveI : Nonempty α := ⟨(tail l).head h⟩
    (tail l).getLastV = l.getLastV

theorem headV_eq_getLastV_reverse {_ : Nonempty α} {l : List α} :
    l.headV = l.reverse.getLastV

theorem getLastV_eq_headV_reverse {_ : Nonempty α} {l : List α} :
    l.getLastV = l.reverse.headV
```

### `Erase.lean` (4)

| V lemma | Counterpart | Annotation | Status |
|---------|-------------|------------|--------|
| `headV_eraseP_mem` | `head_eraseP_mem` (line 306) | `@[grind ←]` | create |
| `getLastV_eraseP_mem` | `getLast_eraseP_mem` (line 310) | `@[grind ←]` | create |
| `headV_erase_mem` | `head_erase_mem` (line 533) | none | create |
| `getLastV_erase_mem` | `getLast_erase_mem` (line 536) | none | create |

#### Suggested signatures

```lean
-- head_eraseP_mem : (xs.eraseP p).head h ∈ xs
-- V variant: keep ne_nil proof for the ∈ to be meaningful, add Nonempty.
@[grind ←]
theorem headV_eraseP_mem {xs : List α} {p : α → Bool} (h : xs.eraseP p ≠ []) :
    haveI : Nonempty α := ⟨(xs.eraseP p).head h⟩
    (xs.eraseP p).headV ∈ xs

@[grind ←]
theorem getLastV_eraseP_mem {xs : List α} {p : α → Bool} (h : xs.eraseP p ≠ []) :
    haveI : Nonempty α := ⟨(xs.eraseP p).head h⟩
    (xs.eraseP p).getLastV ∈ xs

theorem headV_erase_mem [BEq α] (xs : List α) (a : α) (h : xs.erase a ≠ []) :
    haveI : Nonempty α := ⟨(xs.erase a).head h⟩
    (xs.erase a).headV ∈ xs

theorem getLastV_erase_mem [BEq α] (xs : List α) (a : α) (h : xs.erase a ≠ []) :
    haveI : Nonempty α := ⟨(xs.erase a).head h⟩
    (xs.erase a).getLastV ∈ xs
```

### `Find.lean` (6)

| V lemma | Counterpart | Annotation | Status |
|---------|-------------|------------|--------|
| `headV_filterMap` | `head_filterMap` (line 128) | none | create |
| `getLastV_filterMap` | `getLast_filterMap` (line 136) | none | create |
| `headV_filter` | `head_filter` (line 336) | none | create |
| `getLastV_filter` | `getLast_filter` (line 344) | none | create |
| `headV_flatten` | `head_flatten` (line 153) | `@[grind =]` | create |
| `getLastV_flatten` | `getLast_flatten` (line 158) | `@[grind =]` | create |

#### Suggested signatures

```lean
-- head_filterMap : (l.filterMap f).head h = (l.findSome? f).get (...)
-- V variant: keep ne_nil to derive the Nonempty witness.
theorem headV_filterMap {f : α → Option β} {l : List α} (h : (l.filterMap f) ≠ []) :
    haveI : Nonempty β := ⟨(l.filterMap f).head h⟩
    (l.filterMap f).headV = (l.findSome? f).get (by simp_all [Option.isSome_iff_ne_none])

theorem getLastV_filterMap {f : α → Option β} {l : List α} (h : (l.filterMap f) ≠ []) :
    haveI : Nonempty β := ⟨(l.filterMap f).head h⟩
    (l.filterMap f).getLastV = (l.reverse.findSome? f).get (by simp_all [Option.isSome_iff_ne_none])

theorem headV_filter {p : α → Bool} {l : List α} (h : (l.filter p) ≠ []) :
    haveI : Nonempty α := ⟨(l.filter p).head h⟩
    (l.filter p).headV = (l.find? p).get (by simp_all [Option.isSome_iff_ne_none])

theorem getLastV_filter {p : α → Bool} {l : List α} (h : (l.filter p) ≠ []) :
    haveI : Nonempty α := ⟨(l.filter p).head h⟩
    (l.filter p).getLastV = (l.reverse.find? p).get (by simp_all [Option.isSome_iff_ne_none])

-- head_flatten : (flatten L).head (...) = (L.findSome? head?).get (...)
-- V variant: keep the existential condition for Nonempty witness.
@[grind =]
theorem headV_flatten {L : List (List α)} (h : ∃ l, l ∈ L ∧ l ≠ []) :
    haveI : Nonempty α := let ⟨l, _, hl⟩ := h; ⟨l.head hl⟩
    (flatten L).headV = (L.findSome? head?).get (by simpa using h)

@[grind =]
theorem getLastV_flatten {L : List (List α)} (h : ∃ l, l ∈ L ∧ l ≠ []) :
    haveI : Nonempty α := let ⟨l, _, hl⟩ := h; ⟨l.head hl⟩
    (flatten L).getLastV = (L.reverse.findSome? getLast?).get (by simpa using h)
```

### Other files (13)

| V lemma | File | Counterpart | Annotation | Status |
|---------|------|-------------|------------|--------|
| `getLastV_attach` | Attach.lean | `getLast_attach` (line 620) | `@[simp, grind =]` | create |
| `headV_filter_mem` | Sublist.lean | `head_filter_mem` (line 323) | none | create |
| `getLastV_filter_mem` | Sublist.lean | `getLast_filter_mem` (line 326) | none | create |
| `headV_takeWhile` | TakeDrop.lean | `head_takeWhile` (line 332) | none | EXISTS (line 322) |
| `headV_dropWhile_not` | TakeDrop.lean | `head_dropWhile_not` (line 351) | none | EXISTS (line 345) |
| `headV_zipWith` | Zip.lean | `head_zipWith` (line 100) | `@[grind =]` | create |
| `min_eq_headV` | MinMax.lean | `min_eq_head` (line 211) | none | create |
| `max_eq_headV` | MinMax.lean | `max_eq_head` (line 434) | none | create |
| `headV_ofFn` | OfFn.lean | `head_ofFn` (line 144) | none | EXISTS (line 134) |
| `getLastV_ofFn` | OfFn.lean | `getLast_ofFn` (line 149) | none | EXISTS (line 140) |
| `headV_scanl` | Scan/Lemmas.lean | `head_scanl` (line 177) | `@[simp]` | EXISTS (line 180) |
| `getLastV_scanl` | Scan/Lemmas.lean | `getLast_scanl` (line 189) | none | EXISTS (line 193) |
| `headV_scanr` | Scan/Lemmas.lean | `head_scanr` (line 288) | `@[simp]` | EXISTS (line 292) |
| `getLastV_scanr` | Scan/Lemmas.lean | `getLast_scanr` (line 297) | `@[grind =]` | EXISTS (line 301) |
| `headV_take` | Nat/TakeDrop.lean | `head_take` (line 81) | none | create |
| `getLastV_take` | Nat/TakeDrop.lean | `getLast_take` (line 100) | none | create |

#### Suggested signatures (for lemmas that need to be created)

```lean
-- getLast_attach : xs.attach.getLast h = ⟨xs.getLast (...), ...⟩
-- V variant: keep ne_nil for Nonempty witness.
@[simp, grind =]
theorem getLastV_attach {xs : List α} (h : xs.attach ≠ []) :
    haveI : Nonempty { x // x ∈ xs } := ⟨⟨xs.head (by simpa using h), head_mem _⟩⟩
    xs.attach.getLastV = ⟨xs.getLastV, getLastV_mem (by simpa using h)⟩

-- head_filter_mem : (xs.filter p).head h ∈ xs
-- V variant: keep ne_nil for Nonempty and membership truth.
theorem headV_filter_mem (xs : List α) (p : α → Bool) (h : xs.filter p ≠ []) :
    haveI : Nonempty α := ⟨(xs.filter p).head h⟩
    (xs.filter p).headV ∈ xs

theorem getLastV_filter_mem (xs : List α) (p : α → Bool) (h : xs.filter p ≠ []) :
    haveI : Nonempty α := ⟨(xs.filter p).head h⟩
    (xs.filter p).getLastV ∈ xs

-- head_zipWith : (zipWith f as bs).head h = f (as.head ...) (bs.head ...)
-- V variant: keep ne_nil for Nonempty and to ensure as/bs are nonempty.
@[grind =]
theorem headV_zipWith {f : α → β → γ} (h : (List.zipWith f as bs) ≠ []) :
    haveI : Nonempty γ := ⟨f (as.head (by rintro rfl; simp_all)) (bs.head (by rintro rfl; simp_all))⟩
    (List.zipWith f as bs).headV = f as.headV bs.headV

-- min_eq_head : l.min hl = l.head hl  (given Pairwise condition)
-- V variant: keep ne_nil (needed for min) and Pairwise condition.
theorem min_eq_headV {α : Type u} [Min α] {l : List α} (hl : l ≠ [])
    (h : l.Pairwise (fun a b => min a b = a)) :
    haveI : Nonempty α := ⟨l.head hl⟩
    l.min hl = l.headV

theorem max_eq_headV {α : Type u} [Max α] {l : List α} (hl : l ≠ [])
    (h : l.Pairwise (fun a b => max a b = a)) :
    haveI : Nonempty α := ⟨l.head hl⟩
    l.max hl = l.headV

-- head_take : (l.take i).head h = l.head (...)
-- V variant: keep ne_nil for Nonempty witness.
theorem headV_take {l : List α} {i : Nat} (h : l.take i ≠ []) :
    haveI : Nonempty α := ⟨(l.take i).head h⟩
    (l.take i).headV = l.headV

-- getLast_take : (l.take i).getLast h = l[i-1]?.getD (l.getLast ...)
-- V variant: the RHS involves getD and getLast which complicates things.
-- Keep ne_nil for Nonempty.
theorem getLastV_take {l : List α} {i : Nat} (h : l.take i ≠ []) :
    haveI : Nonempty α := ⟨(l.take i).head h⟩
    (l.take i).getLastV = l[i - 1]?.getD l.getLastV
```

#### Existing signatures (for reference / annotation audit)

```lean
theorem headV_takeWhile {p : α → Bool} {l : List α} (w : l.takeWhile p ≠ []) :
    haveI : Nonempty α := ⟨(l.takeWhile p).head w⟩
    (l.takeWhile p).headV = l.headV

theorem headV_dropWhile_not (p : α → Bool) {l : List α} (w : l.dropWhile p ≠ []) :
    haveI : Nonempty α := ⟨(l.dropWhile p).head w⟩
    p ((l.dropWhile p).headV) = false

@[grind =] theorem headV_ofFn {n} {f : Fin n → α} (h : 0 < n) :
    haveI : Nonempty α := ⟨f ⟨0, h⟩⟩
    (ofFn f).headV = f ⟨0, h⟩

@[grind =] theorem getLastV_ofFn {n} {f : Fin n → α} (h : ofFn f ≠ []) :
    (ofFn f).getLast h = f ⟨n - 1, Nat.sub_one_lt (mt ofFn_eq_nil_iff.2 h)⟩

@[simp] theorem headV_scanl {f : β → α → β} :
    haveI : Nonempty β := ⟨b⟩
    (scanl f b l).headV = b

theorem getLastV_scanl {f : β → α → β} :
    haveI : Nonempty β := ⟨b⟩
    (scanl f b l).getLastV = foldl f b l

@[simp] theorem headV_scanr {f : α → β → β} :
    haveI : Nonempty β := ⟨b⟩
    (scanr f b l).headV = foldr f b l

@[grind =] theorem getLastV_scanr {f : α → β → β} :
    haveI : Nonempty β := ⟨b⟩
    (scanr f b l).getLastV = b
```

## Notes

- `getElemV_of_mem`: `∃ i, xs｢i｣ = a` (drops bound from existential). Already exists.
- `mem_iff_getElemV`: `a ∈ xs ↔ ∃ i, xs｢i｣ = a`. Already exists.
- `eq_getElemV_of_length_eq_one`: `l = [l｢0｣]` when `l.length = 1`. Create.
- Head/getLast V variants replace `l.head h` with `l.headV` and `l.getLast h` with `l.getLastV`.
  The proof `h : l ≠ []` is dropped when possible, kept when needed for Nonempty witness.
- Proofs: most follow from `simp [headV_eq_head, ...]` or `rw [← head_eq_headV]; exact ...`.
- Many V variants listed in the original plan already exist in the source. The "EXISTS" entries
  above only need annotation auditing (covered by other steps), not creation.

## Revised counts

| Category | Originally listed | Already exist | Not applicable | To create |
|----------|-------------------|---------------|----------------|-----------|
| Part A getElem | ~55 | ~30 | ~8 | ~17 |
| Part B head/getLast | ~48 | ~36 | 0 | ~12 |
| **Total** | **~103** | **~66** | **~8** | **~29** |
