# Step 1.1: Array V Lemma Parity

Status: good; Refinement Needed: no

## Goal

Create 32 V variant lemmas in `src/Init/Data/Array/Lemmas.lean` (11 `backV` + 21 `getElemV`)
and 1 in `src/Init/Data/Array/MapIdx.lean` (`backV_mapIdx`).

## Signature conventions

- `backV` is `{_ : Nonempty α}`-gated: no explicit `0 < xs.size` proof.
- `getElemV` uses `｢i｣` notation and `{_ : Nonempty α}`: no explicit `i < xs.size` proof.
- When nonemptiness is derivable from context (e.g., a concrete element appears), use
  `haveI : Nonempty α := ...` inside the statement instead of a hypothesis.
- Keep hypotheses that are needed for the *statement* to be true (e.g., `i ≠ j`, `0 < ys.size`).

## `backV` lemmas (11 in Lemmas.lean)

| V lemma | Counterpart | Annotation | Action | Suggested signature |
|---------|-------------|------------|--------|---------------------|
| `backV_singleton` | `back_singleton` | `@[grind =]` | create | `theorem backV_singleton {a : α} : haveI : Nonempty α := ⟨a⟩; #[a].backV = a` |
| `backV_eq_getElemV` | `back_eq_getElem` | `@[grind =]` | create | `theorem backV_eq_getElemV {_ : Nonempty α} {xs : Array α} : xs.backV = xs｢xs.size - 1｣` |
| `backV_mem` | `back_mem` | `@[simp]` | create | `theorem backV_mem {xs : Array α} (h : 0 < xs.size) : haveI : Nonempty α := ⟨xs.back h⟩; xs.backV ∈ xs` |
| `backV_pop` | `back_pop` | none | create | `theorem backV_pop {xs : Array α} (h : 1 < xs.size) : haveI : Nonempty α := ⟨xs.back (by omega)⟩; xs.pop.backV = xs｢xs.size - 2｣` |
| `backV_append_of_size_pos` | `back_append_of_size_pos` | `@[simp]` | create | `theorem backV_append_of_size_pos {xs ys : Array α} (h : 0 < ys.size) : haveI : Nonempty α := ⟨ys.back h⟩; (xs ++ ys).backV = ys.backV` |
| `backV_append` | `back_append` | `@[grind =]` | create | `theorem backV_append {_ : Nonempty α} {xs ys : Array α} : (xs ++ ys).backV = if ys.isEmpty then xs.backV else ys.backV` |
| `backV_append_right` | `back_append_right` | none | create | `theorem backV_append_right {xs ys : Array α} (h : 0 < ys.size) : haveI : Nonempty α := ⟨ys.back h⟩; (xs ++ ys).backV = ys.backV` |
| `backV_append_left` | `back_append_left` | none | create | `theorem backV_append_left {xs ys : Array α} (w : 0 < (xs ++ ys).size) (h : ys.size = 0) : haveI : Nonempty α := ⟨(xs ++ ys).back w⟩; (xs ++ ys).backV = xs.backV` |
| `backV_filter_of_pos` | `back_filter_of_pos` | none | create | `theorem backV_filter_of_pos {p : α → Bool} {xs : Array α} (w : 0 < xs.size) (h : p (xs.back w) = true) : haveI : Nonempty α := ⟨xs.back w⟩; (filter p xs).backV = xs.backV` |
| `backV_filterMap_of_eq_some` | `back_filterMap_of_eq_some` | none | create | `theorem backV_filterMap_of_eq_some {f : α → Option β} {xs : Array α} {w : 0 < xs.size} {b : β} (h : f (xs.back w) = some b) : haveI : Nonempty β := ⟨b⟩; (filterMap f xs).backV = b` |
| `backV_replicate` | `back_replicate` | `@[simp]` | create | `theorem backV_replicate {a : α} (w : 0 < n) : haveI : Nonempty α := ⟨a⟩; (replicate n a).backV = a` |

## `backV` in MapIdx.lean (1 lemma)

| V lemma | Counterpart | Annotation | Action | Suggested signature |
|---------|-------------|------------|--------|---------------------|
| `backV_mapIdx` | `back_mapIdx` | `@[simp, grind =]` | create | `theorem backV_mapIdx {xs : Array α} {f : Nat → α → β} (h : 0 < xs.size) : haveI : Nonempty β := ⟨f (xs.size - 1) (xs.back h)⟩; (xs.mapIdx f).backV = f (xs.size - 1) (xs.backV)` |

## `getElemV` lemmas (21 in Lemmas.lean)

| V lemma | Counterpart | Annotation | Action | Suggested signature |
|---------|-------------|------------|--------|---------------------|
| `getElemV_push_eq` | `getElem_push_eq` | `@[simp]` | create | `theorem getElemV_push_eq {xs : Array α} {x : α} : haveI : Nonempty α := ⟨x⟩; (xs.push x)｢xs.size｣ = x` |
| `getElemV_push` | `getElem_push` | `@[grind =]` | create | `theorem getElemV_push {_ : Nonempty α} {xs : Array α} {x : α} {i : Nat} : (xs.push x)｢i｣ = if i < xs.size then xs｢i｣ else x` |
| `getElemV_set_self` | `getElem_set_self` | `@[simp]` | create | `theorem getElemV_set_self {xs : Array α} {i : Nat} (h : i < xs.size) {v : α} : haveI : Nonempty α := ⟨v⟩; (xs.set i v)｢i｣ = v` |
| `getElemV_set_ne` | `getElem_set_ne` | `@[simp]` | create | `theorem getElemV_set_ne {_ : Nonempty α} {xs : Array α} {i : Nat} (h' : i < xs.size) {v : α} {j : Nat} (h : i ≠ j) : (xs.set i v)｢j｣ = xs｢j｣` |
| `getElemV_set` | `getElem_set` | `@[grind =]` | create | `theorem getElemV_set {_ : Nonempty α} {xs : Array α} {i : Nat} (h' : i < xs.size) {v : α} {j : Nat} : (xs.set i v)｢j｣ = if i = j then v else xs｢j｣` |
| `set_getElemV_self` | `set_getElem_self` | `@[simp]` | create | `theorem set_getElemV_self {_ : Nonempty α} {xs : Array α} {i : Nat} (h : i < xs.size) : xs.set i xs｢i｣ = xs` |
| `getElemV_setIfInBounds` | `getElem_setIfInBounds` | `@[grind =]` | create | `theorem getElemV_setIfInBounds {_ : Nonempty α} {xs : Array α} {i : Nat} {a : α} {j : Nat} : (xs.setIfInBounds i a)｢j｣ = if i = j ∧ j < xs.size then a else xs｢j｣` |
| `getElemV_setIfInBounds_self` | `getElem_setIfInBounds_self` | `@[simp]` | create | `theorem getElemV_setIfInBounds_self {xs : Array α} {i : Nat} {a : α} (h : i < xs.size) : haveI : Nonempty α := ⟨a⟩; (xs.setIfInBounds i a)｢i｣ = a` |
| `getElemV_setIfInBounds_ne` | `getElem_setIfInBounds_ne` | `@[simp]` | create | `theorem getElemV_setIfInBounds_ne {_ : Nonempty α} {xs : Array α} {i : Nat} {a : α} {j : Nat} (h : i ≠ j) : (xs.setIfInBounds i a)｢j｣ = xs｢j｣` |
| `getElemV_filter` | `getElem_filter` | `@[grind ←]` | create | `theorem getElemV_filter {xs : Array α} {p : α → Bool} {i : Nat} (h : i < (xs.filter p).size) : haveI : Nonempty α := ⟨(xs.filter p)[i]⟩; p (xs.filter p)｢i｣` |
| `getElemV_append` | `getElem_append` | `@[grind =]` | create | `theorem getElemV_append {_ : Nonempty α} {xs ys : Array α} {i : Nat} : (xs ++ ys)｢i｣ = if i < xs.size then xs｢i｣ else ys｢i - xs.size｣` |
| `getElemV_append_left` | `getElem_append_left` | `@[simp]` | create | `theorem getElemV_append_left {xs ys : Array α} {i : Nat} (hlt : i < xs.size) : haveI : Nonempty α := ⟨xs[i]⟩; (xs ++ ys)｢i｣ = xs｢i｣` |
| `getElemV_append_right` | `getElem_append_right` | `@[simp]` | create | `theorem getElemV_append_right {_ : Nonempty α} {xs ys : Array α} {i : Nat} (hle : xs.size ≤ i) : (xs ++ ys)｢i｣ = ys｢i - xs.size｣` |
| `getElemV_modify` | `getElem_modify` | `@[grind =]` | create | `theorem getElemV_modify {_ : Nonempty α} {xs : Array α} {j i : Nat} : (xs.modify j f)｢i｣ = if j = i ∧ i < xs.size then f xs｢i｣ else xs｢i｣` |
| `getElemV_swap` | `getElem_swap` | `@[grind =]` | create | `theorem getElemV_swap {xs : Array α} {i j : Nat} {hi : i < xs.size} {hj : j < xs.size} {k : Nat} : haveI : Nonempty α := ⟨xs[i]⟩; (xs.swap i j)｢k｣ = if k = i then xs｢j｣ else if k = j then xs｢i｣ else xs｢k｣` |
| `getElemV_swap_right` | `getElem_swap_right` | `@[simp]` | create | `theorem getElemV_swap_right {xs : Array α} {i j : Nat} {hi hj} : haveI : Nonempty α := ⟨xs[i]⟩; (xs.swap i j hi hj)｢j｣ = xs｢i｣` |
| `getElemV_swap_left` | `getElem_swap_left` | `@[simp]` | create | `theorem getElemV_swap_left {xs : Array α} {i j : Nat} {hi hj} : haveI : Nonempty α := ⟨xs[j]⟩; (xs.swap i j hi hj)｢i｣ = xs｢j｣` |
| `getElemV_swap_of_ne` | `getElem_swap_of_ne` | `@[simp]` | create | `theorem getElemV_swap_of_ne {_ : Nonempty α} {xs : Array α} {i j k : Nat} {hi hj} (hi' : k ≠ i) (hj' : k ≠ j) : (xs.swap i j hi hj)｢k｣ = xs｢k｣` |
| `getElemV_swapIfInBounds` | `getElem_swapIfInBounds` | `@[grind =]` | create | `theorem getElemV_swapIfInBounds {_ : Nonempty α} {xs : Array α} {i j k : Nat} : (xs.swapIfInBounds i j)｢k｣ = if k = i ∧ j < xs.size then xs｢j｣ else if k = j ∧ i < xs.size then xs｢i｣ else xs｢k｣` |
| `getElemV_replace` | `getElem_replace` | `@[grind =]` | create | `theorem getElemV_replace {_ : Nonempty α} [BEq α] [LawfulBEq α] {xs : Array α} {a b : α} {i : Nat} : (xs.replace a b)｢i｣ = if xs｢i｣ == a ∧ i < xs.size then if a ∈ xs.take i then a else b else xs｢i｣` |
| `getElemV_ofFn` | `getElem_ofFn` | `@[simp]` | create | `theorem getElemV_ofFn {f : Fin n → α} {i : Nat} (h : i < n) : haveI : Nonempty α := ⟨f ⟨i, h⟩⟩; (ofFn f)｢i｣ = f ⟨i, h⟩` |

## Notes

- For `getElemV_modify`: the condition needs `i < xs.size` in the `if` because `modify` is a no-op
  when `j ≥ xs.size`, so without this guard the `f xs｢i｣` branch would not be correct.
  Similarly, `getElemV_setIfInBounds` needs `j < xs.size` in the condition.
- For `getElemV_replace`: needs `i < xs.size` guard in the condition since `replace` only affects
  in-bounds elements, and `getElemV` returns `Classical.ofNonempty` out of bounds.
- For `getElemV_swapIfInBounds`: the conjuncts `j < xs.size` and `i < xs.size` are needed because
  `swapIfInBounds` is a no-op when either index is out of bounds.
- `backV_append_of_size_pos` and `backV_append_right` have similar statements; both are kept for
  consistency with the proof-taking variants.
- `backV_pop` requires `1 < xs.size` (not just nonemptiness) because `pop` reduces size by 1, and
  we need `pop` to still be nonempty.
