# Step 5: Verification

Status: good; Refinement Needed: no

## Goal
Verify that the cleanup is complete and correct.

## 5.1 Clean build
```bash
make -j$(nproc) -C build/release
```
Must complete with zero errors.

## 5.2 Full test suite
```bash
CTEST_PARALLEL_LEVEL="$(nproc)" CTEST_OUTPUT_ON_FAILURE=1 \
  make -C build/release -j "$(nproc)" test
```
All tests must pass.

## 5.3 Spot-check simp with V variants
Verify that `simp` can close goals using V variants. For example:
- A goal involving `xs[i]` with proof `h` should be simplified via `getElem_eq_getElemV`
  to use `getElemV`, and then further simplified by V-form simp lemmas.
- A goal involving `l.head h` should be simplified to `l.headV` and then closed.

## 5.4 Annotation audit
Quick grep to verify:
- No `@[simp]` on proof-taking lemmas (excluding bridge lemmas)
- All bridge lemmas have `@[simp, grind norm]`
- All V variant lemmas that mirror annotated proof-taking lemmas have matching annotations

## 5.5 Parity check
For a sample of operations (e.g., `back`/`backV`, `head`/`headV`, `minKey`/`minKeyV`),
manually verify that every proof-taking lemma has a V counterpart.
