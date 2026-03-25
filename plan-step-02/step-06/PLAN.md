# Step 2.6: `src/Std/Data/HashMap/RawLemmas.lean` — 2 create + 2 annotate

Status: not started

## File context

- File: `src/Std/Data/HashMap/RawLemmas.lean`
- Variable context: `{α : Type u} {β : Type v}`, `{m : Raw α β}`, with `[BEq α] [Hashable α]` in scope
- Raw HashMap also uses `getElemV` / `m｢a｣` notation; all lemmas require `(h : m.WF)` parameter
- `Raw.getV [BEq α] [Hashable α] {_ : Nonempty β} (m : Raw α β) (a : α) : β := m.getD a Classical.ofNonempty`

## Lemmas to create

### 1. `getV_eq_getElem`

**Counterpart**: `get_eq_getElem` (line 254)
```
theorem get_eq_getElem {a : α} {h} : get m a h = m[a]'h := rfl
```

**Annotation**: `@[simp, grind =]`

**Suggested signature**:
```lean
@[simp, grind =]
theorem getV_eq_getElem [EquivBEq α] [LawfulHashable α] {_ : Nonempty β} (h : m.WF) {a : α}
    (h' : a ∈ m) :
    m｢a｣ = m[a]'h'
```

**Notes**: Reverse direction of existing `getElem_eq_getElemV` (line 526). Proof: `(getElem_eq_getElemV h).symm`.

### 2. `getV_getElem?`

**Counterpart**: `get_getElem?` (line 351)
```
theorem get_getElem? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {h'} :
    m[a]?.get h' = m[a]'((mem_iff_isSome_getElem? h).mpr h')
```

**Annotation**: `@[grind =]`

**Suggested signature**:
```lean
@[grind =]
theorem getV_getElem? [EquivBEq α] [LawfulHashable α] {_ : Nonempty β} (h : m.WF) {a : α}
    {h' : (m[a]?).isSome} :
    m[a]?.get h' = m｢a｣
```

**Notes**: Bridges `Option.get` on `getElem?` to the V variant. Proof: combine `get_getElem? h` with `getElem_eq_getElemV h`.

## Lemmas to annotate

### 3. `getKeyV_inter` (add `@[simp]`)

**Existing** (line 2093):
```lean
theorem getKeyV_inter [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    (m₁ ∩ m₂).getKeyV k =
    if k ∈ m₂ then m₁.getKeyV k else Classical.ofNonempty
```

**Counterpart**: `getKey_inter` (line 2042)

**Action**: Add `@[simp]` before `theorem getKeyV_inter`.

### 4. `getKeyV_diff` (add `@[simp]`)

**Existing** (line 2429):
```lean
theorem getKeyV_diff [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    (m₁ \ m₂).getKeyV k =
    if k ∈ m₂ then Classical.ofNonempty else m₁.getKeyV k
```

**Counterpart**: `getKey_diff` (line 2378)

**Action**: Add `@[simp]` before `theorem getKeyV_diff`.

## Placement guidance

- Place `getV_eq_getElem` in the getElemV section (after line 538) or near `get_eq_getElem` (line 254).
- Place `getV_getElem?` similarly, near `get_getElem?` (line 351) or in the getElemV section.
- For annotations, add the attribute in-place before the existing theorem.

## Differences from step-05 (HashMap/Lemmas.lean)

- All lemmas take explicit `(h : m.WF)` parameter.
- No `getKeyV_eq` annotation needed (Raw HashMap's `getKeyV_eq_of_mem` is at line 872 but not listed in the plan for this file).
