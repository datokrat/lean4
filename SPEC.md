# V Variants Cleanup — Specification

Status: good; Refinement Needed: no

## Background

The previous task added noncomputable `V` variants for collection operations across the Lean 4
standard library. These variants require only a `[Nonempty]` instance instead of a proof (e.g.,
`i < xs.size` or `l ≠ []`). Bridge lemmas like `getElem_eq_getElemV` with `@[simp, grind norm]`
were created to normalize proof-taking forms into V forms during automation. The `@[simp]`/`@[grind]`
annotations on proof-taking variant lemmas were then removed (or are in the process of being removed).

The codebase currently has build errors (expected) and incomplete V lemma coverage.

## Requirements

### R1: Full parity with proof-taking operations
For every lemma about a proof-taking operation, there must be a corresponding V variant lemma.
This applies to ALL proof-taking lemmas, not just those with `@[simp]`/`@[grind]` annotations.

Proof-taking operations in scope:
- `getElem` (with bound proof) → `getElemV`
- `head` (with `h : l ≠ []`) → `headV`
- `getLast` (with `h : l ≠ []`) → `getLastV`
- `back` (with `h : 0 < xs.size`) → `backV`
- `get` (with containment proof) → `getV`
- `getKey` (with containment proof) → `getKeyV`
- `getEntry` (with proof) → `getEntryV`
- `min`/`max` (with isEmpty proof) → `minV`/`maxV`
- `minKey`/`maxKey` (with isEmpty proof) → `minKeyV`/`maxKeyV`
- `minEntry`/`maxEntry` (with proof) → `minEntryV`/`maxEntryV`
- `atIdx` (with bound proof) → `atIdxV`
- `entryAtIdx`/`keyAtIdx` (with proof) → `entryAtIdxV`/`keyAtIdxV`
- `getGE`/`getGT`/`getLE`/`getLT` and key/entry variants → V variants

### R2: Annotation consistency condition
When removing `@[simp]` or `@[grind]` (any grind variant: `@[grind =]`, `@[grind norm]`, etc.)
from a proof-taking lemma, a correspondingly annotated V-variant lemma MUST exist. If no V
counterpart exists, one must be ADDED before removing the annotation. This is a hard coupling —
annotation removal and V-lemma addition are atomic. This applies equally to `simp` and `grind`
annotations; both must be transferred to V variants.

### R3: High-quality public API
- Lemma signatures must be consistent with library standards
- Annotations must match: if the proof-taking version had `@[simp]`, the V version gets `@[simp]`;
  if it had `@[grind =]`, the V version gets `@[grind =]`; and so on for all annotation variants
- Bridge lemmas must all have `@[simp, grind norm]`

### R4: Fix build errors
The build is currently broken due to the annotation changes. Errors must be resolved, but this
comes LAST since earlier work will add many of the needed V-form simp lemmas.

## Non-goals
- Adding new V variant *definitions* (those are already done)
- Changing the V variant implementation pattern
- Completing `!` variant coverage (separate concern; uses `[Inhabited]`)
- Modifying `DHashMap.Raw` WF-proof annotations (WF is orthogonal to V/non-V distinction)

## Design decisions
- **Ordering**: V lemma additions → annotation cleanup → build error fixes → verification
- **DHashMap.Raw**: `@[simp]` on `Raw` lemmas like `get?_insert_self (h : m.WF)` is NOT an
  annotation hygiene issue. The WF proof is inherent to Raw types and orthogonal to the V variant
  distinction (which is about `Nonempty (β k)` vs `k ∈ m` for value retrieval).
- **Ext wrapper types**: Verify whether they inherit coverage or need independent lemmas.
- **Cascade risk**: Adding new `@[simp]` V-form lemmas may break other proofs. Build after
  each major batch.
