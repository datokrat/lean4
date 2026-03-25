# Step 1.7: List/Scan/Lemmas.lean V Lemma Parity

Status: not started

## File

`src/Init/Data/List/Scan/Lemmas.lean`

## Scan V lemmas — 6 create

| V lemma | Counterpart | Annotation | Suggested signature |
|---------|-------------|------------|---------------------|
| `headV_scanl` | `head_scanl` (line 174) | `@[simp]` | `@[simp] theorem headV_scanl {f : β → α → β} : haveI : Nonempty β := ⟨b⟩; (scanl f b l).headV = b` |
| `headV_scanr` | `head_scanr` (line 276) | `@[simp]` | `@[simp] theorem headV_scanr {f : α → β → β} : haveI : Nonempty β := ⟨b⟩; (scanr f b l).headV = foldr f b l` |
| `getLastV_scanl` | `getLast_scanl` (line 181) | none | `theorem getLastV_scanl {f : β → α → β} : haveI : Nonempty β := ⟨b⟩; (scanl f b l).getLastV = foldl f b l` |
| `getLastV_scanr` | `getLast_scanr` (line 281) | `@[grind =]` | `@[grind =] theorem getLastV_scanr {f : α → β → β} : haveI : Nonempty β := ⟨b⟩; (scanr f b l).getLastV = b` |
| `getElemV_scanl` | `getElem_scanl` (line 144) | `@[simp, grind =]` | `@[simp, grind =] theorem getElemV_scanl {f : α → β → α} (h : i < (scanl f a l).length) : (scanl f a l)｢i｣ = foldl f a (l.take i)` |
| `getElemV_scanr` | `getElem_scanr` (line 305) | `@[simp, grind =]` | `@[simp, grind =] theorem getElemV_scanr {f : α → β → β} (h : i < (scanr f b l).length) : (scanr f b l)｢i｣ = foldr f b (l.drop i)` |

**Notes:**
- `headV_scanl`: The proof-taking version has `h : scanl f b l ≠ []`, which is always true (`scanl` is never empty). The V variant drops this proof. Uses `haveI : Nonempty β := ⟨b⟩` since `b` is available to witness nonemptiness.
- `headV_scanr`: Same pattern — `scanr` is never empty. Uses `haveI` with `⟨b⟩`.
- `getLastV_scanl`: Same pattern. The `getLast_scanl` counterpart has `h : scanl f b l ≠ []` which is always true.
- `getLastV_scanr`: Same pattern.
- `getElemV_scanl`: Retains `h : i < (scanl f a l).length` because the RHS `foldl f a (l.take i)` depends on `i` being in range for the statement to be meaningful. Without it, for out-of-bounds `i`, the LHS would be `Classical.ofNonempty` but the RHS would be `foldl f a (l.take i)` which is a real value — so the equality wouldn't hold. The `haveI` is `⟨a⟩` or derived from `h`. Since `h` gives us an element (via the scanl), the `Nonempty` instance can be derived.
- `getElemV_scanr`: Same reasoning — needs `h` to ensure the equality. RHS `foldr f b (l.drop i)` is a real value regardless of `i`.
- All six lemmas follow the `haveI` pattern since `Nonempty` can be witnessed by the initial accumulator value (`a` or `b`).
