# Step 1.5: List/Nat/Basic.lean V Lemma Parity

Status: good; Refinement Needed: no

## File

`src/Init/Data/List/Nat/Basic.lean`

## getElemV — 2 create

| V lemma | Counterpart | Annotation | Suggested signature |
|---------|-------------|------------|---------------------|
| `getElemV_intersperse_two_mul` | `getElem_intersperse_two_mul` (line 160) | `@[simp]` | `@[simp] theorem getElemV_intersperse_two_mul {l : List α} {sep : α} {i : Nat} (h : 2 * i < (l.intersperse sep).length) : haveI : Nonempty α := ⟨sep⟩; (l.intersperse sep)｢2 * i｣ = l｢i｣` |
| `getElemV_intersperse_two_mul_add_one` | `getElem_intersperse_two_mul_add_one` (line 165) | `@[simp]` | `@[simp] theorem getElemV_intersperse_two_mul_add_one {l : List α} {sep : α} {i : Nat} (h : 2 * i + 1 < (l.intersperse sep).length) : haveI : Nonempty α := ⟨sep⟩; (l.intersperse sep)｢2 * i + 1｣ = sep` |

**Notes:**
- Both lemmas retain a length hypothesis `h` because:
  - `getElemV_intersperse_two_mul`: The RHS is `l｢i｣`, and we need to know `2 * i` is in bounds to ensure `i < l.length` (derivable from `h`). Without the hypothesis, the statement is false for out-of-bounds indices (LHS would be `Classical.ofNonempty` but RHS would also be `Classical.ofNonempty` — actually both sides agree). Need to verify whether the statement can be made unconditional.
  - `getElemV_intersperse_two_mul_add_one`: The RHS is just `sep`, so without the bound the LHS could be `Classical.ofNonempty` which differs from `sep`. So `h` is needed.
- The `haveI : Nonempty α := ⟨sep⟩` can be derived from `sep` in both cases, or from the list element via `h`.
- Alternative: these could use `haveI` pattern if the hypothesis is kept: `haveI : Nonempty α := ⟨sep⟩`.
