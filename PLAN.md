# V Variants Cleanup — Master Plan

Status: good; Refinement Needed: no

## Context

The previous task (described in `V_VARIANTS_PLAN.md`) added noncomputable `V` variants for
collection operations, created bridge lemmas, and began removing `@[simp]`/`@[grind]` from
proof-taking variants. The codebase now has build errors and incomplete V lemma coverage.
This plan addresses the cleanup.

## Scale

- **~120 new V lemmas** to create (Step 1: ~98-103, Step 2: ~22)
- **~44 annotation additions** to existing V lemmas (Step 1: 12, Step 2: ~32)
- **~60 annotation removals** from proof-taking lemmas still annotated (Step 3)
- **~38+ build errors** to fix (Step 4, many will self-resolve)

**NOTE**: Commits 5a80909eff and fbc8c5dd51 already removed annotations from many
proof-taking lemmas WITHOUT creating correspondingly annotated V variants. This plan
ensures all those removals are matched with V counterparts.

## Sub-tasks

### Step 1: Init V lemma parity (`plan-step-01/PLAN.md`)
Add V variant lemmas for Init types to achieve full parity. **~99-104 new lemmas + 12 annotation adds:**
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

### Step 4: Fix build errors (`plan-step-04/PLAN.md`)
Fix remaining build errors after steps 1-3.
- Known: ~38 errors across 6 Init files
- Many will self-resolve from Steps 1-3 (especially Scan, OfFn)
- Expect cascading errors as fixes propagate

### Step 5: Verification (`plan-step-05/PLAN.md`)
- Clean build, full test suite, spot-checks, annotation audit
