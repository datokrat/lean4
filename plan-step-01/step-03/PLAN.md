# Step 1.3: List/Lemmas.lean V Lemma Parity

Status: good; Refinement Needed: no

## File

`src/Init/Data/List/Lemmas.lean`

## headV — 4 create + 5 annotate

### Create

| V lemma | Counterpart | Annotation | Suggested signature |
|---------|-------------|------------|---------------------|
| `headV_map` | `head_map` | `@[simp]` | `@[simp] theorem headV_map {f : α → β} {l : List α} (h : l ≠ []) : haveI : Nonempty β := ⟨f (l.head h)⟩; (map f l).headV = f l.headV` |
| `headV_filterMap_of_eq_some` | `head_filterMap_of_eq_some` | none | `theorem headV_filterMap_of_eq_some {f : α → Option β} {l : List α} (w : l ≠ []) {b : β} (h : f (l.head w) = some b) : haveI : Nonempty β := ⟨b⟩; (filterMap f l).headV = b` |
| `headV_tail` | `head_tail` | `@[simp]` | `@[simp] theorem headV_tail {_ : Nonempty α} {l : List α} : (tail l).headV = l｢1｣` |
| `cons_headV_tail` | `cons_head_tail` | `@[simp, grind =]` | `@[simp, grind =] theorem cons_headV_tail {l : List α} (h : l ≠ []) : haveI : Nonempty α := ⟨l.head h⟩; l.headV :: l.tail = l` |

**Notes:**
- `headV_map`: Needs `(h : l ≠ [])` because when `l = []`, LHS = `Classical.ofNonempty` but RHS = `f Classical.ofNonempty`, which differ in general. Uses `haveI` to derive `Nonempty β` from `f (l.head h)`.
- `headV_filterMap_of_eq_some`: Still needs the `w : l ≠ []` proof since it's needed for `l.head w`. Uses `haveI` to derive `Nonempty β` from `b`.
- `headV_tail`: Unconditional with `[Nonempty α]` — when `l` is nil or singleton, both sides are `Classical.ofNonempty`.
- `cons_headV_tail`: Needs `h : l ≠ []` to make the statement true. Uses `haveI` to derive `Nonempty α`.

### Annotate

These V lemmas already exist but need annotations added:

| V lemma | Required annotation | Current state |
|---------|-------------------|---------------|
| `headV_mem` | `@[simp]` | exists, no `@[simp]` |

The following already have their required annotations (verify only, no action needed):
`headV_append_of_ne_nil`, `headV_append`, `headV_replicate`, `headV_reverse`.

## getLastV — 2 create + 7 annotate

### Create

| V lemma | Counterpart | Annotation | Suggested signature |
|---------|-------------|------------|---------------------|
| `getLastV_map` | `getLast_map` | `@[simp]` | `@[simp] theorem getLastV_map {f : α → β} {l : List α} (h : l ≠ []) : haveI : Nonempty β := ⟨f (l.head h)⟩; (map f l).getLastV = f l.getLastV` |
| `getLastV_tail` | `getLast_tail` | `@[simp, grind =]` | `@[simp, grind =] theorem getLastV_tail {l : List α} (h : l.tail ≠ []) : haveI : Nonempty α := ⟨(tail l).head h⟩; (tail l).getLastV = l.getLastV` |

**Notes:**
- `getLastV_map`: Needs `(h : l ≠ [])` because when `l = []`, LHS = `Classical.ofNonempty` but RHS = `f Classical.ofNonempty`. Uses `haveI` to derive `Nonempty β`.
- `getLastV_tail`: Needs `(h : l.tail ≠ [])` because for `l = [a]`, `tail [a] = []`, so `getLastV [] = Classical.ofNonempty` but `getLastV [a] = a`. Uses `haveI` from `(tail l).head h`.

### Annotate

These V lemmas already exist but need annotations added:

| V lemma | Required annotation | Current state |
|---------|-------------------|---------------|
| `getLastV_cons_cons` | `@[simp, grind =]` | exists, no annotation |
| `getLastV_mem` | `@[simp]` | exists, no `@[simp]` |

The following already have their required annotations (verify only, no action needed):
`getLastV_singleton`, `getLastV_append_of_ne_nil`, `getLastV_append`, `getLastV_replicate`, `getLastV_reverse`.

## getElemV — 3 create

| V lemma | Counterpart | Annotation | Suggested signature |
|---------|-------------|------------|---------------------|
| `getElemV_singleton` | `getElem_singleton` (line 300) | `@[simp]` | `@[simp] theorem getElemV_singleton {a : α} {i : Nat} (h : i < 1) : haveI : Nonempty α := ⟨a⟩; [a]｢i｣ = a` |
| `getElemV_map` | `getElem_map` (line 1344) | `@[simp, grind =]` | `@[simp, grind =] theorem getElemV_map (f : α → β) {l : List α} {i : Nat} (h : i < l.length) : haveI : Nonempty β := ⟨f l[i]⟩; (map f l)｢i｣ = f l｢i｣` |
| `getElemV_append` | `getElem_append` (line 1866) | `@[grind =]` | `@[grind =] theorem getElemV_append {_ : Nonempty α} {l₁ l₂ : List α} {i : Nat} : (l₁ ++ l₂)｢i｣ = if i < l₁.length then l₁｢i｣ else l₂｢i - l₁.length｣` |

**Notes:**
- `getElemV_singleton`: Keeps `h : i < 1` for statement truth. Uses `haveI` from `a`.
- `getElemV_map`: Keeps `(h : i < l.length)` because when out-of-bounds, LHS = `Classical.ofNonempty` but RHS = `f Classical.ofNonempty`, which differ in general. Uses `haveI` from `f l[i]`.
- `getElemV_append`: The proof-taking version has `h : i < (l₁ ++ l₂).length`. V variant drops it. Uses `if` without `dif` since no proof is needed in the branches. Both sides agree out-of-bounds.
