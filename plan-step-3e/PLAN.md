# Step 3e: Comprehensive V Lemma Parity — Full Audit

Status: not started; Refinement Needed: no

## Goal

Fill ALL remaining gaps in V lemma parity across Init and Std. A thorough mechanical audit
of every theorem statement in the codebase revealed ~250 additional proof-taking lemmas
(beyond Steps 1-3c) that lack V counterparts. This step creates them all.

## Scope

Every theorem whose STATEMENT contains a proof-taking operation gets a V counterpart:
- `getElem` with bound proof (`xs[i]'h`)
- `head` with non-empty proof (`l.head h`)
- `getLast` with non-empty proof (`l.getLast h`)
- `get`/`getKey` with membership/bound proof
- `minKey`/`maxKey` with non-empty proof
- `back` with non-empty proof

Exclusions: deprecated lemmas, internal helpers (`.loop`, `.go`, `_aux`, `Internal` namespace),
`getElem_fin` (Fin carries its own proof).

## Annotation handling

This step only CREATES V variant lemmas with matching annotations. The corresponding
removal of `@[simp]`/`@[grind]` from proof-taking counterparts is deferred to
**Step 3f** (`plan-step-3f/PLAN.md`).

## Sub-steps

### 3e.0 GetElem.lean (~12 lemmas)

**Detailed sub-plan**: [step-00/PLAN.md](step-00/PLAN.md)

Generic infrastructure V lemmas polymorphic over all collection types: congr, `?`/`!` bridges,
`some`/`iff` relations.

### 3e.1 Array (~38 lemmas)

**Detailed sub-plan**: [step-01/PLAN.md](step-01/PLAN.md)

Key areas: of_mem, mem_iff, any_eq, eq_iff, getD, back_pop/append, append variants,
modify, swap, swapIfInBounds, replace, extract_loop, DecidableEq, Find, Range/zipIdx.

### 3e.2 List (~103 lemmas)

**Detailed sub-plan**: [step-02/PLAN.md](step-02/PLAN.md)

Split into getElem V variants (~55) and head/getLast V variants (~48).
Covers OfFn, FinRange, Lemmas, Nat/Basic, Nat/Modify, Nat/BEq, Nat/Sublist,
Nat/TakeDrop, Lex, Count, Range, Sublist, Scan, Find, Erase, Attach,
TakeDrop, Zip, MinMax.

### 3e.3 Vector (~14 lemmas)

**Detailed sub-plan**: [step-03/PLAN.md](step-03/PLAN.md)

Covers neg, append_left/right, pop', of_mem, modify, count, extract, eraseIdx,
backV_filter/filterMap.

### 3e.4 BitVec (~22 lemmas)

**Detailed sub-plan**: [step-04/PLAN.md](step-04/PLAN.md)

Covers zero, one, ofFin, cast, allOnes, or, and, xor, not, ushiftRight, extractLsb',
extract, shiftLeftZeroExtend, concat_zero/succ, ofBoolListBE, rev, reverse, cons, neg.

### 3e.5 ByteArray (~4 lemmas)

**Detailed sub-plan**: [step-05/PLAN.md](step-05/PLAN.md)

Will error until `GetElemV ByteArray` instance is added. Covers eq_data, append_left/right, extract.

### 3e.6 Std (~88 lemmas)

**Detailed sub-plan**: [step-06/PLAN.md](step-06/PLAN.md)

Cross-type getElemV consistency:
- HashMap/Lemmas.lean: `getElemV_union_of_mem_right`
- HashMap/RawLemmas.lean: `getElemV_union_of_mem_right`, `getElemV_filterMap'`,
  `getElemV_filter'`, `getElemV_map'`
- ExtHashMap/Lemmas.lean: `getElemV_union_of_mem_right`, `getElemV_filterMap'`,
  `getElemV_filter'`, `getElemV_map'`, `getElemV_eq`, `getKeyV_eq`
- ExtTreeMap/Lemmas.lean: `getElemV_union_of_mem_right`, `getElemV_eq`

HashMap/HashSet any_*/all_*:
- HashMap/Lemmas.lean: 8 V-forms
- HashMap/RawLemmas.lean: 8 V-forms
- HashSet/RawLemmas.lean: 1 V-form

get/getKey V variants across all collection types (~50):
- TreeMap + Raw: getV_eq_getElemV, getKeyV_insert, getKeyV_erase, getKeyV_insertIfNew,
  getV_getKeyV, getV_getElemV
- HashMap + Raw: same set plus getKeyV_insertIfNew (Raw)
- ExtHashMap: getV_eq_getElemV, getKeyV_erase, getV_getKeyV
- ExtTreeMap: getV_eq_getElemV, getKeyV_insert, getKeyV_erase,
  getKeyV_insertIfNew, getV_getKeyV
- DTreeMap + Raw: getV_insert, getV_erase, getKeyV_insert, getKeyV_erase,
  getV_insertIfNew, getKeyV_insertIfNew, getV_getV
- DHashMap + Raw: getV_insert, getV_erase, getKeyV_insert, getKeyV_erase,
  getV_insertIfNew, getV_getV, getV_getKeyV
- TreeSet + Raw: getV_insert, getV_erase, getV_getV, minV_eq_getElemV_toArray
- HashSet + Raw: getV_insert, getV_erase, getV_getV

## Summary

| Sub-step | Area | Lemmas |
|----------|------|--------|
| 3e.0 | GetElem.lean | 12 |
| 3e.1 | Array | 38 |
| 3e.2 | List | 103 |
| 3e.3 | Vector | 14 |
| 3e.4 | BitVec | 22 |
| 3e.5 | ByteArray | 4 |
| 3e.6 | Std | 88 |
| **Total** | | **~281** |
