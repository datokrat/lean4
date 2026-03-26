# Step 3b.3: ExtHashMap + ExtTreeMap V Lemma Parity (Remaining)

Status: good; Refinement Needed: no

## Files

`src/Std/Data/ExtHashMap/Lemmas.lean`, `src/Std/Data/ExtTreeMap/Lemmas.lean`

## Audit results

All candidates from the initial stub have been verified. Every listed lemma
already has a V variant in the source. No new lemmas need to be created.

### `ExtHashMap/Lemmas.lean`

| Candidate | Expected V variant | Status | Details |
|-----------|-------------------|--------|---------|
| `get_eq_getElem` (line 196) | `getV_eq_getElemV` | FALSE POSITIVE | Bridge lemma `get_eq_getElem` relates named `get` to bracket `m[a]'h`. The V counterpart would relate `getV` to `m｢a｣`, but `getElemV` IS `getV` (see `GetElemV` instance at Basic.lean:182), so this is trivially `rfl` and not worth adding. No other Std type has `getV_eq_getElemV` either. |
| `getElem_insert` (line 254) | `getElemV_insert` | FALSE POSITIVE | Already exists at line 394 with `@[grind =]` annotation. |
| `getElem_erase` (line 263) | `getElemV_erase` | FALSE POSITIVE | Already exists at line 412 with `@[grind =]` annotation. |
| `getElem_eq_getD` (line 377) | `getElemV_eq_getD` | FALSE POSITIVE | Already exists as `getElemV_eq_getD_classicalOfNonempty` at line 431 and `getElemV_eq_getD_getElem?` at line 421. |
| `getElem_insertIfNew` (line 785) | `getElemV_insertIfNew` | FALSE POSITIVE | Already exists at line 799 with `@[grind =]` annotation. |
| `getElem_union_of_mem_right` (line 1680) | `getElemV_union_of_not_mem_right` | FALSE POSITIVE | Already exists at line 1728. Also `getElemV_union` (line 1719) and `getElemV_union_of_not_mem_left` (line 1723) exist. |
| `getElem_inter` (line 1939) | `getElemV_inter` | FALSE POSITIVE | Already exists at line 1973 with `@[grind =]` annotation. |

### `ExtTreeMap/Lemmas.lean`

| Candidate | Expected V variant | Status | Details |
|-----------|-------------------|--------|---------|
| `getElem_insert` (line 272) | `getElemV_insert` | FALSE POSITIVE | Already exists at line 367 with `@[grind =]` annotation. |
| `getElem_erase` (line 282) | `getElemV_erase` | FALSE POSITIVE | Already exists at line 404 with `@[grind =]` annotation. |
| `getElem_eq_getD` (line 434) | `getElemV_eq_getD` | FALSE POSITIVE | Already exists as `getElemV_eq_getD_classicalOfNonempty` at line 448 and `getElemV_eq_getD_getElem?` at line 430. |
| `getElem_insertIfNew` (line 807) | `getElemV_insertIfNew` | FALSE POSITIVE | Already exists at line 821 with `@[grind =]` annotation. |
| `getElem_union_of_mem_right` (line 1820) | `getElemV_union_of_not_mem_right` | FALSE POSITIVE | Already exists at line 1868. Also `getElemV_union` (line 1859) and `getElemV_union_of_not_mem_left` (line 1863) exist. |
| `getElem_inter` (line 2076) | `getElemV_inter` | FALSE POSITIVE | Already exists at line 2110 with `@[grind =]` annotation. |
| `getElem_diff` (line 2379) | `getElemV_diff` | FALSE POSITIVE | Already exists at line 2413 with `@[grind =]` annotation. |

## Cross-reference with Step 2.9

Step 2.9 covers **annotation-only** changes for Ext types (adding `@[grind =]` to
existing `getKeyV_*` lemmas). Those are orthogonal to the V lemma parity candidates
audited here, and none of the Step 2.9 entries overlap with these candidates.

## Conclusion

All 14 candidates (7 ExtHashMap + 7 ExtTreeMap) are false positives — V variants
already exist in the source. No action is required for this step.
