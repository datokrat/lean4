# Step 3a.7: Polymorphic Range V Lemma Parity

Status: good; Refinement Needed: no

## Files

`src/Init/Data/Range/Polymorphic/Lemmas.lean`,
`src/Init/Data/Range/Polymorphic/IntLemmas.lean`,
`src/Init/Data/Range/Polymorphic/NatLemmas.lean`

## Summary

All candidates are confirmed gaps (no existing V variants found via grep for
`getElemV_toList` / `getElemV_toArray` in the Polymorphic directory). Each
`getElem_toList_eq` / `getElem_toArray_eq` lemma gets a V variant that:

- Replaces `r.toList[i]'h` with `r.toList｢i｣` (uses `GetElemV`)
- Replaces `.get (proof)` with `.getV` on the RHS (for the polymorphic `Lemmas.lean` versions)
- Drops the proof parameter `h` / `_h`
- Adds `{_ : Nonempty α}` instance parameter (for polymorphic versions)

For the `IntLemmas.lean` / `NatLemmas.lean` concrete versions, the RHS is
already a plain value (e.g. `m + i`), so only the LHS changes.

## Proof strategy

Each V variant can be proved via `simp [getElemV_def, ...]` referencing
the original `getElem` lemma, or via `simp [getElemV_def, getElem?_toList_eq]`.
Alternatively, use `getElem_eq_getElemV` to rewrite and then apply the original.

---

## Lemmas in `Lemmas.lean` (18 lemmas: 9 pairs)

No annotations on any of these (the `@[simp]` versions are in IntLemmas/NatLemmas).

### Template A: Namespaces with `r.lower` (Rcc, Roc, Rco, Roo, Rci, Roi)

These have the form:
```
theorem getElem_toList_eq [classes...] {i h} :
    r.toList[i]'h = (UpwardEnumerable.succMany? <index_expr> r.lower).get
        (isSome_succMany?_of_lt_length_toList h)
```

V variant template:
```
theorem getElemV_toList_eq [classes...] {_ : Nonempty α} {i} :
    r.toList｢i｣ = (UpwardEnumerable.succMany? <index_expr> r.lower).getV
```

And similarly for `getElemV_toArray_eq`.

#### 1. `Rcc.getElemV_toList_eq` (after line ~3051)

Original (line 3046):
```
theorem getElem_toList_eq [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    {i h} :
    r.toList[i]'h = (UpwardEnumerable.succMany? i r.lower).get
        (isSome_succMany?_of_lt_length_toList h)
```

V variant:
```
theorem getElemV_toList_eq [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    {_ : Nonempty α} {i} :
    r.toList｢i｣ = (UpwardEnumerable.succMany? i r.lower).getV
```

#### 2. `Rcc.getElemV_toArray_eq` (after line ~3057)

Original (line 3053):
```
theorem getElem_toArray_eq [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] {i h} :
    r.toArray[i]'h = (UpwardEnumerable.succMany? i r.lower).get
        (isSome_succMany?_of_lt_size_toArray h)
```

V variant:
```
theorem getElemV_toArray_eq [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    {_ : Nonempty α} {i} :
    r.toArray｢i｣ = (UpwardEnumerable.succMany? i r.lower).getV
```

#### 3. `Roc.getElemV_toList_eq` (after line ~3166)

Index expression: `i + 1`. Same class context as Rcc but on `Roc`.

```
theorem getElemV_toList_eq [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    {_ : Nonempty α} {i} :
    r.toList｢i｣ = (UpwardEnumerable.succMany? (i + 1) r.lower).getV
```

#### 4. `Roc.getElemV_toArray_eq` (after line ~3173)

```
theorem getElemV_toArray_eq [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    {_ : Nonempty α} {i} :
    r.toArray｢i｣ = (UpwardEnumerable.succMany? (i + 1) r.lower).getV
```

#### 5. `Rco.getElemV_toList_eq` (after line ~3435)

Uses `[LT α] [DecidableLT α]` and `Rxo.IsAlwaysFinite α`. Index expression: `i`.

```
theorem getElemV_toList_eq [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    {_ : Nonempty α} {i} :
    r.toList｢i｣ = (UpwardEnumerable.succMany? i r.lower).getV
```

#### 6. `Rco.getElemV_toArray_eq` (after line ~3441)

```
theorem getElemV_toArray_eq [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    {_ : Nonempty α} {i} :
    r.toArray｢i｣ = (UpwardEnumerable.succMany? i r.lower).getV
```

#### 7. `Roo.getElemV_toList_eq` (after line ~3550)

Uses `[LT α] [DecidableLT α]` and `Rxo.IsAlwaysFinite α`. Index expression: `i + 1`.

```
theorem getElemV_toList_eq [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    {_ : Nonempty α} {i} :
    r.toList｢i｣ = (UpwardEnumerable.succMany? (i + 1) r.lower).getV
```

#### 8. `Roo.getElemV_toArray_eq` (after line ~3557)

```
theorem getElemV_toArray_eq [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    {_ : Nonempty α} {i} :
    r.toArray｢i｣ = (UpwardEnumerable.succMany? (i + 1) r.lower).getV
```

#### 9. `Rci.getElemV_toList_eq` (after line ~3792)

Uses `[LT α] [DecidableLT α]` and `Rxi.IsAlwaysFinite α`. Index expression: `i`.

```
theorem getElemV_toList_eq [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α]
    {_ : Nonempty α} {i} :
    r.toList｢i｣ = (UpwardEnumerable.succMany? i r.lower).getV
```

#### 10. `Rci.getElemV_toArray_eq` (after line ~3798)

```
theorem getElemV_toArray_eq [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α]
    {_ : Nonempty α} {i} :
    r.toArray｢i｣ = (UpwardEnumerable.succMany? i r.lower).getV
```

#### 11. `Roi.getElemV_toList_eq` (after line ~3899)

Uses `[LT α] [DecidableLT α]` and `Rxi.IsAlwaysFinite α`. Index expression: `i + 1`.

```
theorem getElemV_toList_eq [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α]
    {_ : Nonempty α} {i} :
    r.toList｢i｣ = (UpwardEnumerable.succMany? (i + 1) r.lower).getV
```

#### 12. `Roi.getElemV_toArray_eq` (after line ~3906)

```
theorem getElemV_toArray_eq [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α]
    {_ : Nonempty α} {i} :
    r.toArray｢i｣ = (UpwardEnumerable.succMany? (i + 1) r.lower).getV
```

### Template B: Namespaces with `UpwardEnumerable.least` (Ric, Rio)

These have `[Least? α]` and use `UpwardEnumerable.least` instead of `r.lower`.
They already contain `haveI : Nonempty α := ⟨r.upper⟩` in the original.

#### 13. `Ric.getElemV_toList_eq` (after line ~3277)

Original (line 3271) uses `[Least? α] [LE α] [DecidableLE α]`, `Rxc.IsAlwaysFinite α`,
`LawfulUpwardEnumerableLeast? α`. Index expression: `i`.

```
theorem getElemV_toList_eq [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxc.IsAlwaysFinite α] {_ : Nonempty α} {i} :
    r.toList｢i｣ = (UpwardEnumerable.succMany? (α := α) i UpwardEnumerable.least).getV
```

Note: The original has `haveI : Nonempty α := ⟨r.upper⟩` in the statement body.
The V variant already requires `{_ : Nonempty α}` so this is subsumed.

#### 14. `Ric.getElemV_toArray_eq` (after line ~3285)

```
theorem getElemV_toArray_eq [Least? α] [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLeast? α]
    [Rxc.IsAlwaysFinite α] {_ : Nonempty α} {i} :
    r.toArray｢i｣ = (UpwardEnumerable.succMany? (α := α) i UpwardEnumerable.least).getV
```

#### 15. `Rio.getElemV_toList_eq` (after line ~3661)

Uses `[Least? α] [LT α] [DecidableLT α]`, `Rxo.IsAlwaysFinite α`. Index expression: `i`.

```
theorem getElemV_toList_eq [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] {_ : Nonempty α} {i} :
    r.toList｢i｣ = (UpwardEnumerable.succMany? (α := α) i UpwardEnumerable.least).getV
```

#### 16. `Rio.getElemV_toArray_eq` (after line ~3669)

```
theorem getElemV_toArray_eq [Least? α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLeast? α]
    [Rxo.IsAlwaysFinite α] {_ : Nonempty α} {i} :
    r.toArray｢i｣ = (UpwardEnumerable.succMany? (α := α) i UpwardEnumerable.least).getV
```

### Template C: Namespace Rii (uses `Least?.least?.bind`)

#### 17. `Rii.getElemV_toList_eq` (after line ~4000)

Original (line 3995) uses `[Least? α]`, `Rxi.IsAlwaysFinite α`.
RHS: `(Least?.least?.bind (UpwardEnumerable.succMany? (α := α) i)).get (proof)`.

```
theorem getElemV_toList_eq [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    [Rxi.IsAlwaysFinite α] {_ : Nonempty α} {i} :
    r.toList｢i｣ = (Least?.least?.bind (UpwardEnumerable.succMany? (α := α) i)).getV
```

#### 18. `Rii.getElemV_toArray_eq` (after line ~4007)

```
theorem getElemV_toArray_eq [Least? α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLeast? α]
    [Rxi.IsAlwaysFinite α] {_ : Nonempty α} {i} :
    r.toArray｢i｣ = (Least?.least?.bind (UpwardEnumerable.succMany? (α := α) i)).getV
```

---

## Lemmas in `IntLemmas.lean` (8 lemmas, all `@[simp]`)

All in `namespace Int`. RHS is a concrete `Int` expression so only the LHS changes.
`Int` is `Nonempty` so no explicit instance parameter needed (but we still write
`{_ : Nonempty Int}` per the SIGNATURE_SPEC convention to help `rw`/`simp`).

Actually, since `Int` has a canonical `Nonempty` instance, and the SIGNATURE_SPEC says
to use `{_ : Nonempty α}` for polymorphic lemmas, for concrete `Int`/`Nat` lemmas we
should check: the `getElemV` call will automatically get the `Nonempty Int` instance.
We do NOT need an explicit `{_ : Nonempty Int}` parameter — it's inferred.

### Template for Int:

Original pattern:
```
@[simp]
theorem getElem_toList_rXX {m n : Int} {i : Nat} (_h : i < (RANGE).toList.length) :
    (RANGE).toList[i]'_h = RHS
```

V variant:
```
@[simp]
theorem getElemV_toList_rXX {m n : Int} {i : Nat} :
    (RANGE).toList｢i｣ = RHS
```

#### 19. `Int.getElemV_toList_rco` (after line ~212)

```
@[simp]
theorem getElemV_toList_rco {m n : Int} {i : Nat} :
    (m...n).toList｢i｣ = m + i
```

#### 20. `Int.getElemV_toArray_rco` (after line ~379)

```
@[simp]
theorem getElemV_toArray_rco {m n : Int} {i : Nat} :
    (m...n).toArray｢i｣ = m + i
```

#### 21. `Int.getElemV_toList_rcc` (after line ~608)

```
@[simp]
theorem getElemV_toList_rcc {m n : Int} {i : Nat} :
    (m...=n).toList｢i｣ = m + i
```

#### 22. `Int.getElemV_toArray_rcc` (after line ~758)

```
@[simp]
theorem getElemV_toArray_rcc {m n : Int} {i : Nat} :
    (m...=n).toArray｢i｣ = m + i
```

#### 23. `Int.getElemV_toList_roo` (after line ~987)

```
@[simp]
theorem getElemV_toList_roo {m n : Int} {i : Nat} :
    (m<...n).toList｢i｣ = m + 1 + i
```

#### 24. `Int.getElemV_toArray_roo` (after line ~1137)

```
@[simp]
theorem getElemV_toArray_roo {m n : Int} {i : Nat} :
    (m<...n).toArray｢i｣ = m + 1 + i
```

#### 25. `Int.getElemV_toList_roc` (after line ~1380)

```
@[simp]
theorem getElemV_toList_roc {m n : Int} {i : Nat} :
    (m<...=n).toList｢i｣ = m + 1 + i
```

#### 26. `Int.getElemV_toArray_roc` (after line ~1543)

```
@[simp]
theorem getElemV_toArray_roc {m n : Int} {i : Nat} :
    (m<...=n).toArray｢i｣ = m + 1 + i
```

---

## Lemmas in `NatLemmas.lean` (12 lemmas, all `@[simp]`)

All in `namespace Nat`. Same template approach as Int.

### Template for Nat (rco, rcc, roo, roc):

```
@[simp]
theorem getElemV_COLL_rXX {m n i : Nat} :
    (RANGE).COLL｢i｣ = RHS
```

### Template for Nat (rio, ric):

```
@[simp]
theorem getElemV_COLL_rXX {n i : Nat} :
    (RANGE).COLL｢i｣ = RHS
```

#### 27. `Nat.getElemV_toList_rco` (after line ~308)

```
@[simp]
theorem getElemV_toList_rco {m n i : Nat} :
    (m...n).toList｢i｣ = m + i
```

#### 28. `Nat.getElemV_toArray_rco` (after line ~489)

```
@[simp]
theorem getElemV_toArray_rco {m n i : Nat} :
    (m...n).toArray｢i｣ = m + i
```

#### 29. `Nat.getElemV_toList_rcc` (after line ~727)

```
@[simp]
theorem getElemV_toList_rcc {m n i : Nat} :
    (m...=n).toList｢i｣ = m + i
```

#### 30. `Nat.getElemV_toArray_rcc` (after line ~888)

```
@[simp]
theorem getElemV_toArray_rcc {m n i : Nat} :
    (m...=n).toArray｢i｣ = m + i
```

#### 31. `Nat.getElemV_toList_roo` (after line ~1130)

```
@[simp]
theorem getElemV_toList_roo {m n i : Nat} :
    (m<...n).toList｢i｣ = m + 1 + i
```

#### 32. `Nat.getElemV_toArray_roo` (after line ~1290)

```
@[simp]
theorem getElemV_toArray_roo {m n i : Nat} :
    (m<...n).toArray｢i｣ = m + 1 + i
```

#### 33. `Nat.getElemV_toList_roc` (after line ~1546)

```
@[simp]
theorem getElemV_toList_roc {m n i : Nat} :
    (m<...=n).toList｢i｣ = m + 1 + i
```

#### 34. `Nat.getElemV_toArray_roc` (after line ~1721)

```
@[simp]
theorem getElemV_toArray_roc {m n i : Nat} :
    (m<...=n).toArray｢i｣ = m + 1 + i
```

#### 35. `Nat.getElemV_toList_rio` (after line ~1942)

```
@[simp]
theorem getElemV_toList_rio {n i : Nat} :
    (*...n).toList｢i｣ = i
```

#### 36. `Nat.getElemV_toArray_rio` (after line ~2094)

```
@[simp]
theorem getElemV_toArray_rio {n i : Nat} :
    (*...n).toArray｢i｣ = i
```

#### 37. `Nat.getElemV_toList_ric` (after line ~2249)

```
@[simp]
theorem getElemV_toList_ric {n i : Nat} :
    (*...=n).toList｢i｣ = i
```

#### 38. `Nat.getElemV_toArray_ric` (after line ~2399)

```
@[simp]
theorem getElemV_toArray_ric {n i : Nat} :
    (*...=n).toArray｢i｣ = i
```

---

## Total: 38 new V variant lemmas

- 18 in `Lemmas.lean` (no annotations)
- 8 in `IntLemmas.lean` (all `@[simp]`)
- 12 in `NatLemmas.lean` (all `@[simp]`)

## Implementation notes

1. **Proof strategy**: All proofs should follow `simp [getElemV_def, <original_lemma>]` or
   `simp [getElemV_def, getElem?_toList_eq]`. For the concrete Int/Nat lemmas,
   `simp [getElemV_def, Rco.getElemV_toList_eq]` (referencing the polymorphic V variant)
   or `simp [getElemV_def, Rco.getElem_toList_eq]` (referencing the original).

2. **Placement**: Each V variant should be placed immediately after its corresponding
   original lemma.

3. **No false positives**: All 38 candidates were verified as gaps (grep found zero matches
   for `getElemV_toList` / `getElemV_toArray` in the Polymorphic directory).

4. **Import requirements**: `getElemV_def` and `Option.getV` should already be available
   in these files. Verify during implementation.
