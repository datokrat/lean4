# Step 2.5: `src/Std/Data/HashMap/Lemmas.lean` — 2 create + 3 annotate

Status: not started

## File context

- File: `src/Std/Data/HashMap/Lemmas.lean`
- Variable context: `{α : Type u} {β : Type v} {_ : BEq α} {_ : Hashable α}`, `{m : HashMap α β}`
- HashMap uses `getElemV` / `m｢a｣` notation for V variant access, `m[a]'h` for proof-taking access
- `HashMap.getV {_ : Nonempty β} (m : HashMap α β) (a : α) : β := m.getD a Classical.ofNonempty`

## Lemmas to create

### 1. `getV_eq_getElem`

**Counterpart**: `get_eq_getElem` (line 246)
```
theorem get_eq_getElem {a : α} {h} : get m a h = m[a]'h := rfl
```

**Annotation**: `@[simp, grind =]`

**Suggested signature**:
```lean
@[simp, grind =]
theorem getV_eq_getElem [EquivBEq α] [LawfulHashable α] {_ : Nonempty β} {a : α} (h : a ∈ m) :
    m｢a｣ = m[a]'h
```

**Notes**: This is the reverse direction of the existing `getElem_eq_getElemV` (line 518). The proof follows from `(getElem_eq_getElemV).symm` or `simpa [HashMap.getV] using get_eq_getD`. The membership proof `h` is needed because `m[a]'h` requires it.

### 2. `getV_getElem?`

**Counterpart**: `get_getElem?` (line 342)
```
theorem get_getElem? [EquivBEq α] [LawfulHashable α] {a : α} {h} :
    m[a]?.get h = m[a]'(mem_iff_isSome_getElem?.mpr h)
```

**Annotation**: `@[grind =]`

**Suggested signature**:
```lean
@[grind =]
theorem getV_getElem? [EquivBEq α] [LawfulHashable α] {_ : Nonempty β} {a : α} {h : (m[a]?).isSome} :
    m[a]?.get h = m｢a｣
```

**Notes**: Bridges `Option.get` on `getElem?` to the V variant. Proof approach: combine `get_getElem?` with `getElem_eq_getElemV`.

## Lemmas to annotate

### 3. `getKeyV_eq` (add `@[simp, grind =]`)

**Existing** (line 855):
```lean
theorem getKeyV_eq_of_mem [LawfulBEq α] {_ : Nonempty α} {k : α} (h : k ∈ m) :
    m.getKeyV k = k :=
  getKeyV_eq_of_contains h
```

**Counterpart**: `getKey_eq` (line 639, no annotation)

**Action**: Add `@[simp, grind =]` before `theorem getKeyV_eq_of_mem`. Note: the counterpart `getKey_eq` itself has no annotation, but the V variant should get one per the plan.

### 4. `getKeyV_inter` (add `@[simp]`)

**Existing** (line 2091):
```lean
theorem getKeyV_inter [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} {k : α} :
    (m₁ ∩ m₂).getKeyV k =
    if k ∈ m₂ then m₁.getKeyV k else Classical.ofNonempty
```

**Counterpart**: `getKey_inter` (line 2063, has `@[simp]` — see `getKey_inter` block)

**Action**: Add `@[simp]` before `theorem getKeyV_inter`. Check whether the counterpart `getKey_inter` has `@[simp]` (it does not appear to have it inline; verify at implementation time).

### 5. `getKeyV_diff` (add `@[simp]`)

**Existing** (line 2409):
```lean
theorem getKeyV_diff [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} {k : α} :
    (m₁ \ m₂).getKeyV k =
    if k ∈ m₂ then Classical.ofNonempty else m₁.getKeyV k
```

**Counterpart**: `getKey_diff` (line 2381)

**Action**: Add `@[simp]` before `theorem getKeyV_diff`.

## Placement guidance

- Place `getV_eq_getElem` near line 246 (after `get_eq_getElem`) or in the getElemV section (after line 529).
- Place `getV_getElem?` near line 342 (after `get_getElem?`) or in the getElemV section.
- For annotations, add the attribute in-place before the existing theorem.
