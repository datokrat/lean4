# V Variants Cleanup — Master Plan

Status: good; Refinement Needed: no

## Context

The previous task (described in `V_VARIANTS_PLAN.md`) added noncomputable `V` variants for
collection operations, created bridge lemmas, and began removing `@[simp]`/`@[grind]` from
proof-taking variants. The codebase now has build errors and incomplete V lemma coverage.
This plan addresses the cleanup.

## Scale

- **~125-130 new V lemmas** to create (Step 1: ~99-104, Step 2: ~26)
- **~35 annotation additions** to existing V lemmas (Step 1: 3, Step 2: ~32)
- **~60 annotation removals** from proof-taking lemmas still annotated (Step 3)
- **~131 additional V lemmas** missed by Steps 1-2 (Step 3a: 125 Init, Step 3b: 6 Std)
- **~74 annotation removals** from proof-taking lemmas covered by Steps 3a/3b (Step 3c)
- **~38+ build errors** to fix (Step 4, many will self-resolve)

**NOTE**: Commits 5a80909eff and fbc8c5dd51 already removed annotations from many
proof-taking lemmas WITHOUT creating correspondingly annotated V variants. This plan
ensures all those removals are matched with V counterparts.

## Sub-tasks

### Step 1: Init V lemma parity (`plan-step-01/PLAN.md`)
Add V variant lemmas for Init types to achieve full parity. **~99-104 new lemmas + 3 annotation adds:**
- Array `backV`: 12 new lemmas (Lemmas.lean + MapIdx.lean)
- Array `getElemV`: 20 new lemmas (incl. append_left/right, ofFn)
- Vector `backV`: 10 new lemmas
- Vector `getElemV`: 24 new lemmas (currently ZERO exist)
- List `headV`: 4 new + 5 annotation adds on existing
- List `getLastV`: 2 new + 7 annotation adds on existing
- List `getElemV`: 11 new lemmas (incl. map, Nat/Modify.lean, Nat/Basic.lean)
- **Option `getV`**: 10-15 new lemmas (bind, map, join, guard, ite, filter, etc.)
- Scan V lemmas: 6 (headV/getLastV/getElemV for scanl/scanr)

### Step 2: Std V lemma parity (`plan-step-02/PLAN.md`)
Fix annotation gaps and verify parity for Std collection types. **~22 new lemmas + ~26 annotation adds:**
- 7 `maxKeyV` lemmas each for TreeMap + DTreeMap (14 total, no annotations)
- ~8 HashMap/DHashMap new V lemmas (`getV_eq_getElem`, `getV_getElem?` across 4 files)
- 21 `@[grind =]` additions across 5 Ext type files + DTreeMap/Raw
- ~5 HashMap/DHashMap annotation adds (`getKeyV_eq`, `getKeyV_inter`, `getKeyV_diff`)
- TreeSet/TreeMap `atIdxV`, range queries: at parity (non-V also minimal)

### Step 3: Annotation cleanup (`plan-step-03/PLAN.md`)
Remove `@[simp]`/`@[grind]` from proof-taking variant lemmas:
- ~57 annotation removals, each coupled with V counterpart existence
- All grind annotation variants handled (`@[grind =]`, `@[grind ←]`, `@[grind norm]`, etc.)
- Bridge lemmas retain `@[simp, grind norm]`

### Step 3a: Init remaining V lemma parity (`plan-step-3a/PLAN.md`)
A comprehensive audit revealed ~200 additional proof-taking lemmas in Init that lack V variant
counterparts. Steps 1-2 focused on core value-describing lemmas but missed utility lemmas
(sizeOf, attach, pmap, erase, insertIdx, etc.) and entire file areas (BitVec, ByteArray,
String, Polymorphic Range). This step fills those gaps.
- GetElem.lean: 1
- Array: 20 (Attach, Erase, InsertIdx, Mem, Zip, remaining Lemmas)
- List: 12 (Attach, Nat/Erase, Nat/InsertIdx, Nat/Basic, Nat/TakeDrop)
- Vector: 23 (Algebra, Attach, Erase, Extract, Find, InsertIdx, Zip, remaining Lemmas, OfFn)
- BitVec: 31 + GetElemV instance prerequisite (Lemmas, Bitblast, Bootstrap, Basic)
- ByteArray + String: 0 (blocked on missing GetElemV instances)
- Polymorphic Range: 38 (Lemmas, IntLemmas, NatLemmas)

### Step 3b: Std remaining V lemma parity (`plan-step-3b/PLAN.md`)
The same audit revealed ~40 additional proof-taking lemmas in Std that lack V variant
counterparts, primarily `getElem_insert`, `getElem_erase`, `getElem_eq_getD`, and
`getElem_diff`/`inter`/`union` across all collection types.
- TreeMap (bundled + Raw): 4
- HashMap (bundled + Raw): 0 (all false positives)
- ExtHashMap + ExtTreeMap: 0 (all false positives)
- DTreeMap + HashSet: 2

### Step 3c: Annotation cleanup for Steps 3a/3b (`plan-step-3c/PLAN.md`)
Remove `@[simp]`/`@[grind]` from proof-taking variant lemmas whose V counterparts are
created in Steps 3a and 3b. Same pattern as Step 3 but covering the ~74 annotation
removals needed for the additional ~127 V lemmas from Steps 3a/3b.
- 22 files affected across Init (no Std removals needed)
- Array: 11, List: 6, Vector: 16, BitVec: 20, Range: 20
- Must execute AFTER Steps 3a/3b complete

### Step 3e: Comprehensive V lemma parity — full audit
A thorough audit of every proof-taking lemma across Init and Std revealed ~250 additional
lemmas needing V counterparts. This includes ALL lemmas whose statement contains a
proof-taking operation (`getElem` with bound proof, `head` with `h : l ≠ []`,
`getLast` with proof, `get` with membership/bound, `getKey` with membership,
`minKey`/`maxKey` with non-empty proof), excluding only deprecated and internal helpers.

#### 3e.0 GetElem.lean (~12 lemmas)
- `getElemV_congr`, `getElemV_congr_coll`, `getElemV_congr_idx`
- `getElemV?_pos` (V-form of `getElem?_pos`), `getElemV!_pos`
- `getV_getElemV?` (V-form of `get_getElem?`)
- `getElemV?_eq_some_iff`, `some_eq_getElemV?_iff`, `getElemV_of_getElemV?`
- `of_getElemV_eq`, `some_getElemV_eq_getElemV?_iff`, `getElemV?_eq_some_getElemV_iff`

#### 3e.1 Array (~38 lemmas)
- Lemmas.lean: `getElemV_of_mem`, `mem_iff_getElemV`, V-form of `any_eq`,
  `getElemV_swapIfInBounds_of_size_le_left`, `getElemV_swapIfInBounds_of_size_le_right`,
  `getElemV_eq_iff`, `getElemV_eq_getElem` (identity), `getD_getElemV`,
  `backV_pop`, `backV_append`, `getElemV_append`, `getElemV_append_left`,
  `getElemV_append_right`, `getElemV_of_append`, `getElemV_eq_getD`,
  `getElemV_modify`, `getElemV_swap` (`@[grind =]`), `getElemV_swap_of_ne`,
  `getElemV_swapIfInBounds`, `getElemV_replace_of_ne`,
  `filterMap_replicate_of_some` (V-form), `mem_of_getElemV`,
  `getElemV_extract_loop_ge`
- Erase.lean: `mem_eraseIdx_iff_getElemV`, `getElemV_eraseIdx_of_lt`, `getElemV_eraseIdx_of_ge`
- DecidableEq.lean: V-forms of `isEqv_iff_rel`, `isEqv_eq_decide`, `beq_eq_decide`
- Find.lean: `findIdx_getElemV`, `getElemV_zero_flatten`, V-forms of
  `not_of_lt_findIdx`, `le_findIdx_of_not`, `lt_findIdx_of_not`, `findIdx_eq`,
  `mem_of_find`, `get_find`
- Range.lean: `getElemV_zipIdx`, `fst_eq_of_mem_zipIdx` (V), `mem_zipIdx` (V)

#### 3e.2 List (~103 lemmas)
getElem V variants:
- OfFn.lean: `ofFn_getElemV` (`@[simp]`)
- FinRange.lean: `getElemV_finRange`
- Lemmas.lean: `getElemV_eq_iff`, `getElemV_of_eq`, `getElemV_zero`,
  `getElemV_cons`, `getElemV_cons_length`, `getElemV_concat_length`,
  `eq_getElemV_of_length_eq_one/two/three/four`,
  `getElemV_of_mem`, `mem_of_getElemV`, `mem_iff_getElemV`,
  `getElemV_eq_getD`, `getD_getElemV`, `getElemV_append`,
  `getElemV_append_left`, `getElemV_append_right`,
  `getElemV_of_append`, `getElemV_reverse`,
  `getElemV_filter`, `getElemV_map`, `getElemV_tail`,
  `getElemV_dropLast`, `getElemV_replace`, `getElemV_replace_of_ne`,
  `getElemV_insert`, `ext_getElemV_iff`,
  `getElemV_take`, `getElemV_drop`, `getElemV_zipWith`, `getElemV_zip`
- Nat/Basic.lean: `getElemV_eq_getElemV_reverse`, `getElemV_intersperse_two_mul`,
  `getElemV_eq_getElemV_intersperse_two_mul`, `mem_eraseIdx_iff_getElemV`
- Nat/Modify.lean: `getElemV_modifyHead`, `getElemV_modifyHead_zero`,
  `getElemV_modifyHead_succ`, `getElemV_modify`, `getElemV_modify_eq`,
  `getElemV_modify_ne`
- Nat/BEq.lean: V-forms of `isEqv_eq_decide`, `beq_eq_decide`
- Nat/Sublist.lean: V-form of `suffix_iff_getElem`
- Nat/TakeDrop.lean: `headV_take`, `getLastV_take`, `drop_length_cons` (V)
- Lex.lean: V-forms of `lex_eq_true_iff_exists`, `lex_eq_false_iff_exists`
- Count.lean: `boole_getElemV_le_countP`, `boole_getElemV_le_count`
- Range.lean: `getElemV_zipIdx`
- Sublist.lean: V-forms of `prefix_iff_getElem`
- Scan/Lemmas.lean: `getElemV_succ_scanl`
- Find.lean: `findIdx_getElemV`, V-forms of `not_of_lt_findIdx`, `le_findIdx_of_not`,
  `lt_findIdx_of_not`, `findIdx_eq`

head/getLast V variants:
- Lemmas.lean: `headV_eq_getElemV`, `getElemV_zero_eq_headV`,
  `headV_eq_iff_headV`, `headV_map`, `headV_filter_of_pos`,
  `headV_filterMap_of_eq_some`, `headV_append`/`_of_ne_nil`/`_left`/`_right`,
  `headV_replicate`, `headV_reverse`, `headV_dropLast`,
  `headV_replace`, `headV_insert`, `headV_tail`,
  `cons_headV_tail`,
  `getLastV_eq_getElemV`, `getElemV_length_sub_one_eq_getLastV`,
  `getLastV_eq_getLastD`, `getLastV_eq_iff_getLast?_eq_some`,
  `getLastV_mem`, `getLastV_mem_getLast`,
  `getLastV_map`, `getLastV_concat`,
  `getLastV_append`/`_of_ne_nil`/`_right`/`_left`,
  `getLastV_reverse`, `getLastV_replicate`,
  `getLastV_dropLast`, `getLastV_tail`,
  `getLastV_filterMap_of_eq_some`,
  `headV_eq_getLastV_reverse`, `getLastV_eq_headV_reverse`
- Erase.lean: `headV_eraseP_mem`, `getLastV_eraseP_mem`,
  `headV_erase_mem`, `getLastV_erase_mem`
- Find.lean: `headV_filterMap`, `getLastV_filterMap`, `headV_filter`, `getLastV_filter`,
  `headV_flatten`, `getLastV_flatten`, V-form of `find`, `mem_of_find`
- Attach.lean: `getLastV_attach`
- Sublist.lean: `headV_filter_mem`, `getLastV_filter_mem`,
  V-forms of `Sublist` head/getLast lemmas, `IsPrefix` head, `IsSuffix` getLast
- TakeDrop.lean: `headV_takeWhile`, `headV_dropWhile_not`
- Zip.lean: `headV_zipWith`
- MinMax.lean: `min_eq_headV`, `max_eq_headV`
- OfFn.lean: `headV_ofFn`, `getLastV_ofFn`
- Scan/Lemmas.lean: `headV_scanl`, `getLastV_scanl`, `headV_scanr`, `getLastV_scanr`

#### 3e.3 Vector (~14 lemmas)
- Algebra.lean: `getElemV_neg` (`@[simp, grind =]`)
- Lemmas.lean: `getElemV_append_left` (`@[simp]`), `getElemV_append_right` (`@[simp]`),
  `getElemV_pop'`, `getElemV_of_mem`, `getElemV?_of_mem`, `getElemV_modify`
- Count.lean: `boole_getElemV_le_countP`, `boole_getElemV_le_count`
- Extract.lean: `getElemV?_extract_of_lt`
- Erase.lean: `getElemV?_eraseIdx_of_lt`, `getElemV?_eraseIdx_of_ge`
- Find.lean: `backV_filter_of_pos`, `backV_filterMap_of_eq_some`

#### 3e.4 BitVec (~22 lemmas)
- Lemmas.lean: `getElemV_zero` (`@[simp, grind =]`), `getElemV_one` (`@[simp, grind =]`),
  `getElemV_ofFin` (`@[simp]`), `getElemV_cast` (`@[simp, grind =]`),
  `getElemV_allOnes` (`@[simp, grind =]`), `getElemV_or` (`@[simp, grind =]`),
  `getElemV_and` (`@[simp, grind =]`), `getElemV_xor` (`@[simp, grind =]`),
  `getElemV_not` (`@[simp, grind =]`), `getElemV_ushiftRight` (`@[simp, grind =]`),
  `getElemV_extractLsb'` (`@[simp, grind =]`), `getElemV_extract` (`@[simp, grind =]`),
  `getElemV_shiftLeftZeroExtend` (`@[simp]`), `getElemV_concat_zero` (`@[simp]`),
  `getElemV_concat_succ` (`@[simp]`), `getElemV_ofBoolListBE` (`@[simp, grind =]`),
  `getElemV_zero_ofNat_zero`, `getElemV_zero_ofNat_one`,
  `getElemV_rev` (`@[grind =]`), `getElemV_reverse` (`@[grind =]`)
- Bootstrap.lean: `getElemV_cons` (`@[grind =]`)
- Bitblast.lean: `getElemV_neg`

#### 3e.5 ByteArray (~4 lemmas, will error until GetElemV instance added)
- Lemmas.lean: `getElemV_eq_getElemV_data`, `getElemV_append_left` (`@[simp]`),
  `getElemV_append_right`, `getElemV_extract`

#### 3e.6 Std (~88 lemmas)
Cross-type consistency gaps for getElemV:
- HashMap/Lemmas.lean: `getElemV_union_of_mem_right`
- HashMap/RawLemmas.lean: `getElemV_union_of_mem_right`, `getElemV_filterMap'`,
  `getElemV_filter'`, `getElemV_map'`
- ExtHashMap/Lemmas.lean: `getElemV_union_of_mem_right`, `getElemV_filterMap'`,
  `getElemV_filter'`, `getElemV_map'`
- ExtTreeMap/Lemmas.lean: `getElemV_union_of_mem_right`

HashMap/HashSet any_*/all_* quantified predicate lemmas:
- HashMap/Lemmas.lean: 8 V-forms of `any_*/all_*` quantified predicate lemmas
- HashMap/RawLemmas.lean: 8 V-forms of same
- HashSet/RawLemmas.lean: 1 V-form of `all_eq_false_iff_exists_mem_getElem`

get/getKey V variants across ALL Std collection types:
- TreeMap + Raw: `getV_eq_getElemV`, `getKeyV_insert`, `getKeyV_erase`, `getKeyV_insertIfNew`,
  `getV_getKeyV`, `getV_getElemV`
- HashMap + Raw: same set, plus `getKeyV_insertIfNew` (Raw)
- ExtHashMap: `getV_eq_getElemV`, `getKeyV_erase`, `getV_getKeyV`
- ExtTreeMap: `getV_eq_getElemV`, `getKeyV_insert`, `getKeyV_erase`,
  `getKeyV_insertIfNew`, `getV_getKeyV`
- DTreeMap + Raw: `getV_insert`, `getV_erase`, `getKeyV_insert`, `getKeyV_erase`,
  `getV_insertIfNew`, `getKeyV_insertIfNew`, `getV_getV`
- DHashMap + Raw: `getV_insert`, `getV_erase`, `getKeyV_insert`, `getKeyV_erase`,
  `getV_insertIfNew`, `getV_getV`, `getV_getKeyV`
- TreeSet + Raw: `getV_insert`, `getV_erase`, `getV_getV`, `minV_eq_getElemV_toArray`
- HashSet + Raw: `getV_insert`, `getV_erase`, `getV_getV`

### Step 3f: Annotation cleanup for Step 3e
Remove `@[simp]`/`@[grind]` from proof-taking variant lemmas whose V counterparts are
created in Step 3e. Same pattern as Steps 3/3c.
- Must execute AFTER Step 3e

### Step 3d: Std Nonempty instance style cleanup
Convert existing Std V lemmas from `[Nonempty β]` (typeclass brackets) to `haveI`/`{_ : Nonempty β}`
(implicit braces) for consistency with Init conventions and better `rw`/`simp` unification.
- Use `haveI : Nonempty β := ⟨v⟩` where a witness like `{v : β}` is in scope (e.g., `getElemV_insert`)
- Use `{_ : Nonempty β}` where no witness is available
- Affects: HashMap, ExtHashMap, TreeMap, ExtTreeMap, TreeSet, DHashMap, DTreeMap, HashSet
- New lemmas from Step 3b should use the corrected `haveI`/`{_:}` style from the start
- This step cleans up only the *existing* Std V lemmas written in Steps 1-2

### Step 4: Fix build errors (`plan-step-04/PLAN.md`)
Fix remaining build errors after steps 1-3.
- Known: ~38 errors across 6 Init files
- Many will self-resolve from Steps 1-3 (especially Scan, OfFn)
- Expect cascading errors as fixes propagate
- Also adds BitVec `GetElemV` instance prerequisite for Step 3a.5

### Step 5: Verification (`plan-step-05/PLAN.md`)
- Clean build, full test suite, spot-checks, annotation audit
