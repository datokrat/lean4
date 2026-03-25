# Step 1.6: Option/Lemmas.lean V Lemma Parity

Status: good; Refinement Needed: no

## File

`src/Init/Data/Option/Lemmas.lean`

## getV — 10 definite + up to 5 conditional creates

### Definite creates (10)

| V lemma | Counterpart | Annotation | Suggested signature |
|---------|-------------|------------|---------------------|
| `getV_bind` | `get_bind` | `@[simp, grind =]` | `@[simp, grind =] theorem getV_bind {_ : Nonempty α} {_ : Nonempty β} {x : Option α} {f : α → Option β} (h : x.isSome) : (x.bind f).getV = (f x.getV).getV` |
| `getV_map` | `get_map` | `@[simp, grind =]` | `@[simp, grind =] theorem getV_map {_ : Nonempty α} {f : α → β} {o : Option α} : (o.map f).getV = f o.getV` |
| `getV_join` | `get_join` | `@[grind =]` | `@[grind =] theorem getV_join {_ : Nonempty α} {x : Option (Option α)} : x.join.getV = x.getV.getV` |
| `getV_guard` | `get_guard` | `@[simp, grind =]` | `@[simp, grind =] theorem getV_guard {_ : Nonempty α} {p : α → Prop} [DecidablePred p] {a : α} (h : p a) : (guard p a).getV = a` |
| `getV_dite` | `get_dite` | `@[simp]` | `@[simp] theorem getV_dite {_ : Nonempty β} {p : Prop} {_ : Decidable p} (b : p → β) (h : p) : (if h' : p then some (b h') else none).getV = b h` |
| `getV_ite` | `get_ite` | `@[simp]` | `@[simp] theorem getV_ite {_ : Nonempty β} {p : Prop} {_ : Decidable p} {b : β} (h : p) : (if p then some b else none).getV = b` |
| `getV_dite'` | `get_dite'` | `@[simp]` | `@[simp] theorem getV_dite' {_ : Nonempty β} {p : Prop} {_ : Decidable p} (b : ¬ p → β) (h : ¬ p) : (if h' : p then none else some (b h')).getV = b h` |
| `getV_ite'` | `get_ite'` | `@[simp]` | `@[simp] theorem getV_ite' {_ : Nonempty β} {p : Prop} {_ : Decidable p} {b : β} (h : ¬ p) : (if p then none else some b).getV = b` |
| `getV_filter` | `get_filter` | `@[simp, grind =]` | `@[simp, grind =] theorem getV_filter {_ : Nonempty α} {x : Option α} {f : α → Bool} (h : (x.filter f).isSome) : (x.filter f).getV = x.getV` |
| `getV_pfilter` | `get_pfilter` | `@[simp, grind =]` | `@[simp, grind =] theorem getV_pfilter {_ : Nonempty α} {o : Option α} {p : (a : α) → o = some a → Bool} (h : (o.pfilter p).isSome) : (o.pfilter p).getV = o.getV` |

**Notes:**
- `getV_bind`: Requires `(h : x.isSome)` to avoid the case where `x = none` and `f Classical.ofNonempty = some b`, which makes LHS = `Classical.ofNonempty` ≠ `b` = RHS. With `h : x.isSome`, `x = some a` for some `a`, so `x.getV = a` and `(x.bind f).getV = (f a).getV = (f x.getV).getV`. Needs both `[Nonempty α]` (for `x.getV` on RHS) and `[Nonempty β]` (for return type).
- `getV_map`: With `[Nonempty α]`, `Nonempty β` follows from `Nonempty.map f`. The statement is unconditional.
- `getV_join`: `x.getV` has type `Option α`, which needs `[Nonempty (Option α)]` — but `Option α` is always `Nonempty` (via `none`). So `[Nonempty α]` suffices for the outer `.getV`.
- `getV_guard`: Needs `h : p a` to ensure `guard p a = some a`. Without it, `guard p a = none` and the LHS is `Classical.ofNonempty`.
- `getV_dite` / `getV_ite` / `getV_dite'` / `getV_ite'`: These replace the `isSome` proof `w` with an explicit hypothesis that the condition holds (or doesn't hold), ensuring the `if` evaluates to `some`. The `[Nonempty β]` is needed for `getV` on the LHS.
- `getV_filter` / `getV_pfilter`: These still need `h : (x.filter f).isSome` because without it the filter could return `none` and the equality wouldn't hold.

### Conditional creates (check during implementation)

| V lemma | Counterpart | Annotation | Suggested signature | Notes |
|---------|-------------|------------|---------------------|-------|
| `getV_none_eq_iff_true` | `get_none_eq_iff_true` | `@[simp]` | `@[simp] theorem getV_none_eq_iff_true {_ : Nonempty α} : (none : Option α).getV = a ↔ True` | Trivially true since `getV none = Classical.ofNonempty`. But the original uses `get` with a proof `h` where `h : none.isSome` is vacuously false — so the original is also trivially true. The V variant may be provable but vacuous. Check if useful. |
| `getV_merge` | `get_merge` | `@[simp]` | `@[simp] theorem getV_merge {_ : Nonempty α} {o o' : Option α} {f : α → α → α} {i : α} [Std.LawfulIdentity f i] : (o.merge f o').getV = f (o.getD i) (o'.getD i)` | Needs `Std.LawfulIdentity` — check if appropriate for V variant. |
| `getV_pbind` | `get_pbind` | `@[simp, grind =]` | `@[simp, grind =] theorem getV_pbind {_ : Nonempty β} {o : Option α} {f : (a : α) → o = some a → Option β} (h : (o.pbind f).isSome) : (o.pbind f).getV = (f o.getV ‹_›).getV` | Dependent types make this tricky — `f` depends on `o = some a`. The V variant can't easily provide `o = some a` proof. Flag for careful review. |
| `getV_pmap` | `get_pmap` | `@[simp, grind =]` | `@[simp, grind =] theorem getV_pmap {_ : Nonempty β} {p : α → Bool} {f : (x : α) → p x → β} {o : Option α} {h : ∀ a, o = some a → p a} (h' : (o.pmap f h).isSome) : (o.pmap f h).getV = f o.getV (h _ ‹_›)` | Similar dependent-type issue as `pbind`. |
| `getV_min` | `get_min` | `@[simp, grind =]` | `@[simp, grind =] theorem getV_min [Min α] {_ : Nonempty α} {o o' : Option α} (h : (min o o').isSome) : (min o o').getV = min o.getV o'.getV` | Needs `h` since `min none none = none`. The `get` version uses separate `isSome_left` / `isSome_right` proofs. The V variant with `[Nonempty α]` can use `getV` directly on `o` and `o'`, but the equality only holds when the min is `some`. Flag for review. |
