# Step 2.7: `src/Std/Data/DHashMap/Lemmas.lean` — 2 create + 3 annotate

Status: not started

## File context

- File: `src/Std/Data/DHashMap/Lemmas.lean`
- Variable context (dep): `{α : Type u} {β : α → Type v} {_ : BEq α} {_ : Hashable α}`, `{m : DHashMap α β}`
- Variable context (Const): `{β : Type v} {m : DHashMap α (fun _ => β)}`
- DHashMap has no `GetElem` instance. The dep `get` takes a membership proof; `Const.get` is the non-dependent version.
- `DHashMap.getV {_ : Nonempty (β a)} (m : DHashMap α β) (a : α) : β a := m.getD a Classical.ofNonempty`
- `DHashMap.Const.getV {_ : Nonempty β} (m : DHashMap α (fun _ => β)) (a : α) : β` (defined via `Const.getD`)

## Important: DHashMap has no getElem

Unlike HashMap, DHashMap has no `GetElem` instance. The plan's reference to `get_eq_getElem` means creating V-variant bridge lemmas analogous to those in HashMap. For DHashMap these bridge the V operations to the proof-taking `get` operations.

Both dependent and Const variants need to be created.

## Lemmas to create

### 1. `getV_eq_get` (dep) — counterpart of `get_eq_getV` reversed

**Existing reverse** (line 690):
```lean
theorem get_eq_getV [LawfulBEq α] {a : α} {h} :
    haveI : Nonempty (β a) := ⟨m.get a h⟩
    m.get a h = m.getV a
```

**Annotation**: `@[simp, grind =]`

**Suggested signature** (dep):
```lean
@[simp, grind =]
theorem getV_eq_get [LawfulBEq α] {a : α} {_ : Nonempty (β a)} (h : a ∈ m) :
    m.getV a = m.get a h
```

**Notes**: Reverse of `get_eq_getV`. Proof: `(get_eq_getV).symm`. Needs `{_ : Nonempty (β a)}` since it starts from `getV`.

### 2. `getV_get?` (dep) — counterpart of `get_get?`

**Counterpart** (line 414):
```lean
theorem get_get? [LawfulBEq α] {a : α} {h} :
    (m.get? a).get h = m.get a (mem_iff_isSome_get?.mpr h)
```

**Annotation**: `@[grind =]`

**Suggested signature** (dep):
```lean
@[grind =]
theorem getV_get? [LawfulBEq α] {a : α} {_ : Nonempty (β a)} {h : (m.get? a).isSome} :
    (m.get? a).get h = m.getV a
```

**Notes**: Bridges `Option.get` on `get?` to V variant. Proof: combine `get_get?` with `get_eq_getV`.

### 3. `Const.getV_eq_get` — counterpart of `Const.get_eq_getV` reversed

**Existing reverse** (line 813):
```lean
namespace Const
theorem get_eq_getV [EquivBEq α] [LawfulHashable α] {a : α} {h} :
    haveI : Nonempty β := ⟨get m a h⟩
    get m a h = getV m a
```

**Annotation**: `@[simp, grind =]`

**Suggested signature**:
```lean
@[simp, grind =]
theorem getV_eq_get [EquivBEq α] [LawfulHashable α] {_ : Nonempty β} {a : α} (h : a ∈ m) :
    Const.getV m a = Const.get m a h
```

### 4. `Const.getV_get?` — counterpart of `Const.get_get?`

**Counterpart** (line 443):
```lean
namespace Const
theorem get_get? [EquivBEq α] [LawfulHashable α] {a : α} {h} :
    (get? m a).get h = get m a (mem_iff_isSome_get?.mpr h)
```

**Annotation**: `@[grind =]`

**Suggested signature**:
```lean
@[grind =]
theorem getV_get? [EquivBEq α] [LawfulHashable α] {_ : Nonempty β} {a : α}
    {h : (Const.get? m a).isSome} :
    (Const.get? m a).get h = Const.getV m a
```

## Lemmas to annotate

### 5. `getKeyV_eq` (add `@[simp, grind =]`)

**Existing** (line 1160):
```lean
theorem getKeyV_eq_of_mem [LawfulBEq α] {_ : Nonempty α} {k : α} (h : k ∈ m) :
    m.getKeyV k = k :=
  getKeyV_eq_of_contains h
```

**Action**: Add `@[simp, grind =]` before `theorem getKeyV_eq_of_mem`.

### 6. `getKeyV_inter` (add `@[simp]`)

**Existing** (line 2675):
```lean
theorem getKeyV_inter [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} {k : α} :
    (m₁ ∩ m₂).getKeyV k =
    if k ∈ m₂ then m₁.getKeyV k else Classical.ofNonempty
```

**Action**: Add `@[simp]` before `theorem getKeyV_inter`.

### 7. `getKeyV_diff` (add `@[simp]`)

**Existing** (line 3072):
```lean
theorem getKeyV_diff [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} {k : α} :
    (m₁ \ m₂).getKeyV k =
    if k ∈ m₂ then Classical.ofNonempty else m₁.getKeyV k
```

**Action**: Add `@[simp]` before `theorem getKeyV_diff`.

## Placement guidance

- Place dep `getV_eq_get` near line 693 (after `get_eq_getV`).
- Place dep `getV_get?` near line 416 (after `get_get?`).
- Place `Const.getV_eq_get` near line 816 (after `Const.get_eq_getV`).
- Place `Const.getV_get?` near line 445 (after `Const.get_get?`).
- For annotations, add the attribute in-place before the existing theorem.

## Note on plan naming

The parent plan uses `getV_eq_getElem` and `getV_getElem?` as V lemma names. Since DHashMap has no `getElem`, the actual lemma names are `getV_eq_get` and `getV_get?` (both dep and Const versions). The "2 create" count in the parent plan counts dep+Const together as one logical item each.
