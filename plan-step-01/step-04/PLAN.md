# Step 1.4: List/Nat/Modify.lean V Lemma Parity

Status: good; Refinement Needed: no

## File

`src/Init/Data/List/Nat/Modify.lean`

## getElemV — 5 create

| V lemma | Counterpart | Annotation | Suggested signature |
|---------|-------------|------------|---------------------|
| `getElemV_modifyHead_zero` | `getElem_modifyHead_zero` (line 49) | `@[simp]` | `@[simp] theorem getElemV_modifyHead_zero {l : List α} {f : α → α} (h : 0 < l.length) : haveI : Nonempty α := ⟨l[0]⟩; (l.modifyHead f)｢0｣ = f l｢0｣` |
| `getElemV_modifyHead_succ` | `getElem_modifyHead_succ` (line 52) | `@[simp]` | `@[simp] theorem getElemV_modifyHead_succ {_ : Nonempty α} {l : List α} {f : α → α} {n : Nat} : (l.modifyHead f)｢n + 1｣ = l｢n + 1｣` |
| `getElemV_modify` | `getElem_modify` (line 208) | `@[grind =]` | `@[grind =] theorem getElemV_modify {_ : Nonempty α} (f : α → α) (i) (l : List α) (j) : (l.modify i f)｢j｣ = if i = j ∧ j < l.length then f l｢j｣ else l｢j｣` |
| `getElemV_modify_eq` | `getElem_modify_eq` (line 215) | `@[simp]` | `@[simp] theorem getElemV_modify_eq {l : List α} (f : α → α) (i) (h : i < l.length) : haveI : Nonempty α := ⟨l[i]⟩; (l.modify i f)｢i｣ = f l｢i｣` |
| `getElemV_modify_ne` | `getElem_modify_ne` (line 218) | `@[simp]` | `@[simp] theorem getElemV_modify_ne {_ : Nonempty α} (f : α → α) {i j} (l : List α) (h : i ≠ j) : (l.modify i f)｢j｣ = l｢j｣` |

**Notes:**
- `getElemV_modifyHead_zero`: Needs `(h : 0 < l.length)` because when `l = []`, LHS = `Classical.ofNonempty` but RHS = `f Classical.ofNonempty`. Uses `haveI` from `l[0]`.
- `getElemV_modifyHead_succ`: Unconditional — when out of bounds, both sides are `Classical.ofNonempty` (since `modifyHead` doesn't change the tail or the length).
- `getElemV_modify`: Needs `∧ j < l.length` in the `if` condition (like the Array counterpart) because when `i = j` and `j ≥ l.length`, LHS = `Classical.ofNonempty` but `f l｢j｣ = f Classical.ofNonempty`.
- `getElemV_modify_eq`: Needs `(h : i < l.length)` for the same reason. Uses `haveI` from `l[i]`.
- `getElemV_modify_ne`: Unconditional (given `i ≠ j`) — when `j ≥ l.length`, both sides are `Classical.ofNonempty`.
