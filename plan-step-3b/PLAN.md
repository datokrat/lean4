# Step 3b: Std Remaining V Lemma Parity

Status: good; Refinement Needed: no

## Goal

Fill the remaining gaps in V lemma parity for Std collection types. The audit found ~40
additional proof-taking lemmas (beyond those covered by Step 2) that lack V variant
counterparts. Step 2 focused on `maxKeyV`, `getV_eq_getElem`, and annotation additions,
but missed `getElem_insert`, `getElem_erase`, `getElem_eq_getD`, `getElem_insertIfNew`,
and set operation lemmas (`getElem_union`, `getElem_inter`, `getElem_diff`).

## Methodology

Same as Step 3a: verify each entry, cross-reference with Step 2, filter deprecated/internal,
write signatures. See `plan-step-3a/PLAN.md` for full methodology.

## Sub-steps

### 3b.1 TreeMap + TreeMap.Raw (~12 lemmas)

**Detailed sub-plan**: [step-01/PLAN.md](step-01/PLAN.md)

TreeMap/Lemmas.lean: getElem_insert, getElem_erase, getElem_eq_getD, getElem_insertIfNew,
getElem_union_of_mem_right, getElem_inter, getElem_diff, minKey_eq_getElem_keysArray.

TreeMap/Raw/Lemmas.lean: getElem_insert, getElem_erase, getElem_eq_getD, getElem_insertIfNew,
getElem_insertMany_list, getElem_union_of_mem_right, getElem_inter, getElem_diff.

### 3b.2 HashMap + HashMap.Raw (~25 lemmas)

**Detailed sub-plan**: [step-02/PLAN.md](step-02/PLAN.md)

HashMap/Lemmas.lean: get_eq_getElem, getElem_insert, getElem_erase, getElem_eq_getD,
getV_eq_getElem, getElem_insertIfNew, getElem_union_of_mem_right, getElem_inter, getElem_diff,
plus 8 any/all iff lemmas.

HashMap/RawLemmas.lean: same pattern — get_eq_getElem, getElem_insert, getElem_erase,
getElem_eq_getD, getV_eq_getElem, getElem_insertIfNew, getElem_union_of_mem_right,
getElem_inter, getElem_diff, plus 8 any/all iff lemmas.

### 3b.3 ExtHashMap + ExtTreeMap (~14 lemmas)

**Detailed sub-plan**: [step-03/PLAN.md](step-03/PLAN.md)

ExtHashMap/Lemmas.lean: get_eq_getElem, getElem_insert, getElem_erase, getElem_eq_getD,
getElem_insertIfNew, getElem_union_of_mem_right, getElem_inter.

ExtTreeMap/Lemmas.lean: getElem_insert, getElem_erase, getElem_eq_getD, getElem_insertIfNew,
getElem_union_of_mem_right, getElem_inter, getElem_diff.

### 3b.4 DTreeMap + HashSet (~6 lemmas)

**Detailed sub-plan**: [step-04/PLAN.md](step-04/PLAN.md)

DTreeMap/Internal/Lemmas.lean: minKey_eq_getElem_keysArray.
DTreeMap/Lemmas.lean: minKey_eq_getElem_keysArray.
DTreeMap/Internal/WF/Lemmas.lean: entryAtIdx_eq_getElem (×2), keyAtIdx_eq_getElem_fst.
HashSet/RawLemmas.lean: all_eq_false_iff_exists_mem_getElem.

## Summary

| Sub-step | Area | Lemmas to create |
|----------|------|-----------------|
| 3b.1 | TreeMap (bundled + Raw) | 4 |
| 3b.2 | HashMap (bundled + Raw) | 0 (all false positives or not meaningful) |
| 3b.3 | ExtHashMap + ExtTreeMap | 0 (all false positives) |
| 3b.4 | DTreeMap + HashSet | 2 |
| **Total** | | **6** |

Note: The audit's original estimate of ~57 was heavily inflated. Most candidates were false
positives (V variants already exist) or not meaningful (any/all iff lemmas where getElem
appears under quantifiers with bound proofs).
