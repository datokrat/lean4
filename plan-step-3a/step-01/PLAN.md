# Step 3a.1: GetElem.lean V Lemma Parity

Status: good; Refinement Needed: no

## File

`src/Init/GetElem.lean`

## Audit results

| V lemma | Counterpart | Annotation | Action | Suggested signature |
|---------|-------------|------------|--------|---------------------|
| `getElemV_congr` (generic) | `getElem_congr` (line 143) | none | SKIP — congruence lemma; the V variant is trivially `congr`/`congrArg` since `getElemV` has no validity proof. Data-structure-specific `getElemV_congr` lemmas exist (TreeMap, HashMap) but those carry additional conditions. The generic one is not needed. | n/a |
| `getElemV_congr_coll` | `getElem_congr_coll` (line 147) | none | SKIP — same reasoning as `getElem_congr`. Generic V variant would be a trivial `congrArg`. | n/a |
| `getElemV_congr_idx` | `getElem_congr_idx` (line 151) | none | SKIP — same reasoning as `getElem_congr`. Generic V variant would be a trivial `congrArg`. | n/a |
| `of_getElemV_eq` | `of_getElem_eq` (line 296) | none | SKIP — this lemma extracts a validity proof `dom c i` from `c[i] = e` (where `h : dom c i` is implicit in the `c[i]` notation). For `getElemV`, there is no validity proof to extract, so a V variant is nonsensical. | n/a |
| `getElemV_cons_zero` | `getElem_cons_zero` (line 346) | `@[simp]` | FALSE POSITIVE — already exists at line 461 | n/a |
| `getElemV_cons_succ` | `getElem_cons_succ` (line 350) | `@[simp]` | FALSE POSITIVE — already exists at line 466 | n/a |
| `getElemV_cons_drop` | `getElem_cons_drop` (line 357) | `@[simp]` | ADD | See below |
| `getElemV_cons_drop_succ_eq_drop` | `getElem_cons_drop_succ_eq_drop` (line 364) | none | SKIP — deprecated alias of `getElem_cons_drop` (since 2025-10-26) | n/a |

## Lemma to add

### `getElemV_cons_drop`

The original:
```lean
@[simp]
theorem getElem_cons_drop {as : List α} {i : Nat} (h : i < as.length) :
    as[i] :: as.drop (i+1) = as.drop i
```

The V variant still needs the `i < as.length` hypothesis because the statement is false when
`i >= as.length` (the LHS would be `garbage :: []` while the RHS would be `[]`). However, it is
still useful: `simp` can apply it when the goal contains `as｢i｣` without needing to match a
specific proof term.

Suggested signature:
```lean
@[simp]
theorem getElemV_cons_drop {as : List α} {i : Nat} {_ : Nonempty α} (h : i < as.length) :
    as｢i｣ :: as.drop (i+1) = as.drop i
```

Proof strategy: rewrite `as｢i｣` to `as[i]'h` using `getElemV_pos` (or `getElem_eq_getElemV`),
then apply `getElem_cons_drop`.

## Summary

Of the 8 candidates, 2 are false positives (already exist), 4 are skipped (congr lemmas where
generic V variants are trivial / `of_getElem_eq` where V variant is nonsensical / deprecated alias),
and **1 lemma needs to be added**: `getElemV_cons_drop`.
