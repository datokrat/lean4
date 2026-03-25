# Step 4: Fix Build Errors

Status: good; Refinement Needed: yes (scope depends on steps 1-3)

## Goal
Fix all remaining build errors after V lemma additions and annotation cleanup.

## Context
Many build errors are caused by `simp` rewriting proof-taking forms into V forms (via bridge
lemmas) but then failing to close the goal because V-form simp lemmas don't exist. Steps 1-3
add these V-form lemmas, which should resolve many errors automatically.

## Known error files (before steps 1-3)

### `Init/Data/List/OfFn.lean` (~5 errors)
- Line 116: unsolved goal in `ofFn_getElem`
- Line 136-137: `headV_ofFn` — unknown identifier `getElemV_zero`
- Lines 141, 150: unsolved goals in `getLastV_ofFn`, `getLast_ofFn`
- Likely fix: add `getElemV_zero` or equivalent lemma. Some may self-resolve from Step 1.

### `Init/Data/Array/DecidableEq.lean` (3 errors)
- Lines 68, 79, 157: unsolved goals / "no goals to be solved"
- Likely cause: simp now rewrites `getElem` to `getElemV`, changing proof state

### `Init/Data/Array/Mem.lean` (1 error)
- Line 28: unsolved goal in `sizeOf_get`
- Likely cause: `getElem_eq_getElemV` simp rewrite

### `Init/Data/Range/Polymorphic/UpwardEnumerable.lean` (~9 errors)
- Lines 289-388: multiple unsolved goals
- Likely cause: `Option.get_eq_getV` simp bridge rewrites `o.get h` to `o.getV`
- Fix: either add `Option.getV` simp lemmas for `succ?`/`succMany?` patterns, or
  rewrite proofs to work with V forms

### `Init/Data/List/Scan/Lemmas.lean` (~18 errors)
- Lines 304-330: multiple unsolved goals in scan-related lemmas
- Likely cause: missing `headV_scanl`, `getElemV_scanl` etc.
- Step 1.5 adds these V lemmas, which should fix most errors

### `Init/Data/List/Sublist.lean` (2 errors)
- Lines 597, 622: unsolved goals in sublist lemmas
- Likely cause: `getElem` → `getElemV` rewriting

## Procedure
1. Build after steps 1-3: `make -j$(nproc) -C build/release`
2. Collect remaining errors
3. For each error:
   a. If caused by missing V simp lemma → add the lemma (should have been caught in steps 1-2)
   b. If caused by proof needing rewrite → adapt proof to work with V forms
   c. If caused by simp taking different path → adjust proof strategy
4. Iterate until clean build
5. Expect cascading errors — fixing one file may reveal errors in downstream files

## Risk: Cascade effects
Adding new `@[simp]` V-form lemmas can cause other proofs to break. This is expected
and manageable — each broken proof typically just needs `simp` arguments adjusted.
