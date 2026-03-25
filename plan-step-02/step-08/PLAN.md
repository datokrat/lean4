# Step 2.8: `src/Std/Data/DHashMap/RawLemmas.lean` — 2 create + 3 annotate

Status: not started

## File context

- File: `src/Std/Data/DHashMap/RawLemmas.lean`
- Variable context (dep): `{α : Type u} {β : α → Type v}`, `{m : Raw α β}`, with `[BEq α] [Hashable α]` in scope
- Variable context (Const): `{β : Type v} {m : DHashMap.Raw α (fun _ => β)} (h : m.WF)`
- All lemmas require `(h : m.WF)` or `(h₁ : m₁.WF) (h₂ : m₂.WF)` parameters
- Same pattern as step-07 but with WF proofs throughout

## Note

`getEntryV`: defined but zero public `getEntry` lemmas exist in DHashMap Raw, so parity holds trivially.

## Lemmas to create

### 1. `getV_eq_get` (dep) — counterpart of `get_eq_getV` reversed

**Existing reverse** (line 699):
```lean
theorem get_eq_getV [LawfulBEq α] (h : m.WF) {a : α} {h'} :
    haveI : Nonempty (β a) := ⟨m.get a h'⟩
    m.get a h' = m.getV a
```

**Annotation**: `@[simp, grind =]`

**Suggested signature** (dep):
```lean
@[simp, grind =]
theorem getV_eq_get [LawfulBEq α] (h : m.WF) {a : α} {_ : Nonempty (β a)} (h' : a ∈ m) :
    m.getV a = m.get a h'
```

**Notes**: Reverse of `get_eq_getV`. Proof: `(get_eq_getV h).symm`.

### 2. `getV_get?` (dep) — counterpart of `get_get?`

**Counterpart** (line 474):
```lean
theorem get_get? [LawfulBEq α] (h : m.WF) {a : α} {h'} :
    (m.get? a).get h' = m.get a ((mem_iff_isSome_get? h).mpr h')
```

**Annotation**: `@[grind =]`

**Suggested signature** (dep):
```lean
@[grind =]
theorem getV_get? [LawfulBEq α] (h : m.WF) {a : α} {_ : Nonempty (β a)}
    {h' : (m.get? a).isSome} :
    (m.get? a).get h' = m.getV a
```

### 3. `Const.getV_eq_get` — counterpart of `Const.get_eq_getV` reversed

**Existing reverse** (line 826):
```lean
namespace Const
theorem get_eq_getV [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {h'} :
    haveI : Nonempty β := ⟨get m a h'⟩
    get m a h' = Const.getV m a
```

**Annotation**: `@[simp, grind =]`

**Suggested signature**:
```lean
@[simp, grind =]
theorem getV_eq_get [EquivBEq α] [LawfulHashable α] {_ : Nonempty β} (h : m.WF) {a : α}
    (h' : a ∈ m) :
    Const.getV m a = Const.get m a h'
```

### 4. `Const.getV_get?` — counterpart of `Const.get_get?`

**Counterpart** (line 503):
```lean
namespace Const
theorem get_get? [EquivBEq α] [LawfulHashable α] (h : m.WF) {a : α} {h'} :
    (get? m a).get h' = get m a ((mem_iff_isSome_get? h).mpr h')
```

**Annotation**: `@[grind =]`

**Suggested signature**:
```lean
@[grind =]
theorem getV_get? [EquivBEq α] [LawfulHashable α] {_ : Nonempty β} (h : m.WF) {a : α}
    {h' : (Const.get? m a).isSome} :
    (Const.get? m a).get h' = Const.getV m a
```

## Lemmas to annotate

### 5. `getKeyV_eq` (add `@[simp, grind =]`)

**Existing** (line 1192):
```lean
theorem getKeyV_eq_of_mem [LawfulBEq α] {_ : Nonempty α} (h : m.WF) {k : α} :
    k ∈ m → m.getKeyV k = k
```

**Action**: Add `@[simp, grind =]` before `theorem getKeyV_eq_of_mem`.

### 6. `getKeyV_inter` (add `@[simp]`)

**Existing** (line 2953):
```lean
theorem getKeyV_inter [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} (h₁ : m₁.WF)
    (h₂ : m₂.WF) {k : α} :
    (m₁ ∩ m₂).getKeyV k =
    if k ∈ m₂ then m₁.getKeyV k else Classical.ofNonempty
```

**Action**: Add `@[simp]` before `theorem getKeyV_inter`.

### 7. `getKeyV_diff` (add `@[simp]`)

**Existing** (line 3454):
```lean
theorem getKeyV_diff [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} :
    (m₁ \ m₂).getKeyV k =
    if k ∈ m₂ then Classical.ofNonempty else m₁.getKeyV k
```

**Action**: Add `@[simp]` before `theorem getKeyV_diff`.

## Placement guidance

- Place dep `getV_eq_get` near line 702 (after `get_eq_getV`).
- Place dep `getV_get?` near line 476 (after `get_get?`).
- Place `Const.getV_eq_get` near line 829 (after `Const.get_eq_getV`).
- Place `Const.getV_get?` near line 505 (after `Const.get_get?`).
- For annotations, add the attribute in-place before the existing theorem.

## Note on plan naming

Same as step-07: the parent plan uses `getV_eq_getElem` names but DHashMap has no `getElem`, so actual names are `getV_eq_get` and `getV_get?`. The "2 create" count in the parent plan counts dep+Const together as one logical item each.
