# Step 3e.6: Std V Lemma Parity (Full Audit)

Status: not started; Refinement Needed: no

## Files

Multiple files under `src/Std/Data/`.

## Goal

Fill ALL remaining V lemma gaps across Std collection types:
1. Cross-type getElemV consistency (map types)
2. HashMap/HashSet any_*/all_* quantified predicate lemmas
3. get/getKey V variants across all collection types

## Part A: Cross-type getElemV consistency (~11 lemmas)

### A1: HashMap/Lemmas.lean

```lean
-- Counterpart: getElem_union_of_mem_right [EquivBEq α] [LawfulHashable α]
--   {k : α} (contains_right : k ∈ m₂) :
--   (m₁ ∪ m₂)[k]'(mem_union_of_right contains_right) = m₂[k]'contains_right
theorem getElemV_union_of_mem_right [EquivBEq α] [LawfulHashable α] {_ : Nonempty β}
    {k : α} (mem : k ∈ m₂) :
    (m₁ ∪ m₂)｢k｣ = m₂｢k｣
```

### A2: HashMap/RawLemmas.lean

```lean
-- Counterpart: getElem_union_of_mem_right [EquivBEq α] [LawfulHashable α] (h₁ : m₁.WF) (h₂ : m₂.WF)
--   {k : α} (mem : k ∈ m₂) :
--   (m₁ ∪ m₂)[k]'(mem_union_of_right h₁ h₂ mem) = m₂[k]'mem
theorem getElemV_union_of_mem_right [EquivBEq α] [LawfulHashable α] {_ : Nonempty β}
    (h₁ : m₁.WF) (h₂ : m₂.WF)
    {k : α} (mem : k ∈ m₂) :
    (m₁ ∪ m₂)｢k｣ = m₂｢k｣
```

Note: `getElemV_filterMap'`, `getElemV_filter'`, `getElemV_map'` already exist in HashMap/RawLemmas.lean
(lines 3829, 4014, 4252). Removing items 3-5 from original plan.

### A3: ExtHashMap/Lemmas.lean

```lean
-- Counterpart: getElem_union_of_mem_right [EquivBEq α] [LawfulHashable α]
--   {k : α} (mem : k ∈ m₂) :
--   (m₁ ∪ m₂)[k]'(mem_union_of_right mem) = m₂[k]'mem
theorem getElemV_union_of_mem_right [EquivBEq α] [LawfulHashable α] {_ : Nonempty β}
    {k : α} (mem : k ∈ m₂) :
    (m₁ ∪ m₂)｢k｣ = m₂｢k｣
```

Note: `getElemV_filterMap'`, `getElemV_filter'`, `getElemV_map'` already exist in ExtHashMap/Lemmas.lean
(lines 3080 for filter', 3273 for map'). But `getElemV_filterMap'` needs checking:

```lean
-- Already exists at line ~3080 (getElemV_filter') and ~3273 (getElemV_map')
-- getElemV_filterMap' does NOT exist yet. Counterpart pattern from TreeMap:
theorem getElemV_filterMap' [EquivBEq α] [LawfulHashable α] {_ : Nonempty γ}
    {f : α → β → Option γ} {k : α} :
    (m.filterMap f)｢k｣ = (m[k]?.bind (f k)).getD Classical.ofNonempty
```

Note: `getElemV_eq` and `getKeyV_eq` for ExtHashMap/ExtTreeMap are about map equivalence (`~m`),
which these types do not support. Removing items 10, 11, 13 from original plan.

### A4: ExtTreeMap/Lemmas.lean

```lean
-- Counterpart: getElem_union_of_mem_right [TransCmp cmp]
--   {k : α} (mem : k ∈ t₂) :
--   (t₁ ∪ t₂)[k]'(mem_union_of_right mem) = t₂[k]'mem
theorem getElemV_union_of_mem_right [TransCmp cmp] {_ : Nonempty β}
    {k : α} (mem : k ∈ t₂) :
    (t₁ ∪ t₂)｢k｣ = t₂｢k｣
```

### Part A Summary Table

| # | V lemma | File | Exists? |
|---|---------|------|---------|
| 1 | `getElemV_union_of_mem_right` | HashMap/Lemmas.lean | NO - add |
| 2 | `getElemV_union_of_mem_right` | HashMap/RawLemmas.lean | NO - add |
| 3 | `getElemV_filterMap'` | HashMap/RawLemmas.lean | YES (line 3829) - skip |
| 4 | `getElemV_filter'` | HashMap/RawLemmas.lean | YES (line 4014) - skip |
| 5 | `getElemV_map'` | HashMap/RawLemmas.lean | YES (line 4252) - skip |
| 6 | `getElemV_union_of_mem_right` | ExtHashMap/Lemmas.lean | NO - add |
| 7 | `getElemV_filterMap'` | ExtHashMap/Lemmas.lean | NO - add |
| 8 | `getElemV_filter'` | ExtHashMap/Lemmas.lean | YES (line 3080) - skip |
| 9 | `getElemV_map'` | ExtHashMap/Lemmas.lean | YES (line 3273) - skip |
| 10 | `getElemV_eq` | ExtHashMap/Lemmas.lean | N/A - no `~m` for ExtHashMap |
| 11 | `getKeyV_eq` | ExtHashMap/Lemmas.lean | N/A - no `~m` for ExtHashMap |
| 12 | `getElemV_union_of_mem_right` | ExtTreeMap/Lemmas.lean | NO - add |
| 13 | `getElemV_eq` | ExtTreeMap/Lemmas.lean | N/A - no `~m` for ExtTreeMap |

**Actual new lemmas in Part A: 5** (items 1, 2, 6, 7, 12)

## Part B: HashMap/HashSet any_*/all_* (~17 lemmas)

The V variant of each any/all lemma replaces proof-indexed `m[a]'h` with `m｢a｣` and
proof-indexed `m.getKey a h` with `m.getKeyV a`. The membership binder `(h : a ∈ m)` stays
because it's the quantifier variable, but `[Nonempty β]` is added.

### HashMap/Lemmas.lean (8)

```lean
-- Counterpart: any_eq_true_iff_exists_mem_getKey_getElem [LawfulHashable α] [EquivBEq α]
--   {p : α → β → Bool} :
--   m.any p = true ↔ ∃ (a : α) (h : a ∈ m), p (m.getKey a h) (m[a]'h)
theorem any_eq_true_iff_exists_mem_getKeyV_getElemV [LawfulHashable α] [EquivBEq α]
    [Nonempty β] {p : α → β → Bool} :
    m.any p = true ↔ ∃ (a : α), a ∈ m ∧ p (m.getKeyV a) (m｢a｣)

-- Counterpart: any_eq_true_iff_exists_mem_getElem [LawfulBEq α]
--   {p : α → β → Bool} :
--   m.any p = true ↔ ∃ (a : α) (h : a ∈ m), p a (m[a]'h)
theorem any_eq_true_iff_exists_mem_getElemV [LawfulBEq α]
    [Nonempty β] {p : α → β → Bool} :
    m.any p = true ↔ ∃ (a : α), a ∈ m ∧ p a (m｢a｣)

-- Counterpart: any_eq_false_iff_forall_mem_getKey_getElem [LawfulHashable α] [EquivBEq α]
--   {p : α → β → Bool} :
--   m.any p = false ↔ ∀ (a : α) (h : a ∈ m), p (m.getKey a h) (m[a]'h) = false
theorem any_eq_false_iff_forall_mem_getKeyV_getElemV [LawfulHashable α] [EquivBEq α]
    [Nonempty β] {p : α → β → Bool} :
    m.any p = false ↔ ∀ (a : α), a ∈ m → p (m.getKeyV a) (m｢a｣) = false

-- Counterpart: any_eq_false_iff_forall_mem_getElem [LawfulBEq α]
--   {p : α → β → Bool} :
--   m.any p = false ↔ ∀ (a : α) (h : a ∈ m), p a (m[a]'h) = false
theorem any_eq_false_iff_forall_mem_getElemV [LawfulBEq α]
    [Nonempty β] {p : α → β → Bool} :
    m.any p = false ↔ ∀ (a : α), a ∈ m → p a (m｢a｣) = false

-- Counterpart: all_eq_true_iff_forall_mem_getKey_getElem [EquivBEq α] [LawfulHashable α]
--   {p : (a : α) → β → Bool} :
--   m.all p = true ↔ ∀ (a : α) (h : a ∈ m), p (m.getKey a h) (m[a]'h)
theorem all_eq_true_iff_forall_mem_getKeyV_getElemV [EquivBEq α] [LawfulHashable α]
    [Nonempty β] {p : (a : α) → β → Bool} :
    m.all p = true ↔ ∀ (a : α), a ∈ m → p (m.getKeyV a) (m｢a｣)

-- Counterpart: all_eq_true_iff_forall_mem_getElem [LawfulBEq α]
--   {p : α → β → Bool} :
--   m.all p = true ↔ ∀ (a : α) (h : a ∈ m), p a (m[a]'h)
theorem all_eq_true_iff_forall_mem_getElemV [LawfulBEq α]
    [Nonempty β] {p : α → β → Bool} :
    m.all p = true ↔ ∀ (a : α), a ∈ m → p a (m｢a｣)

-- Counterpart: all_eq_false_iff_exists_mem_getKey_getElem [EquivBEq α] [LawfulHashable α]
--   {p : (a : α) → β → Bool} :
--   m.all p = false ↔ ∃ (a : α) (h : a ∈ m), p (m.getKey a h) (m[a]'h) = false
theorem all_eq_false_iff_exists_mem_getKeyV_getElemV [EquivBEq α] [LawfulHashable α]
    [Nonempty β] {p : (a : α) → β → Bool} :
    m.all p = false ↔ ∃ (a : α), a ∈ m ∧ p (m.getKeyV a) (m｢a｣) = false

-- Counterpart: all_eq_false_iff_exists_mem_getElem [LawfulBEq α]
--   {p : α → β → Bool} :
--   m.all p = false ↔ ∃ (a : α) (h : a ∈ m), p a (m[a]'h) = false
theorem all_eq_false_iff_exists_mem_getElemV [LawfulBEq α]
    [Nonempty β] {p : α → β → Bool} :
    m.all p = false ↔ ∃ (a : α), a ∈ m ∧ p a (m｢a｣) = false
```

### HashMap/RawLemmas.lean (8)

Same signatures as HashMap/Lemmas.lean, with `(h : m.WF)` added:

```lean
theorem any_eq_true_iff_exists_mem_getKeyV_getElemV [LawfulHashable α] [EquivBEq α]
    [Nonempty β] {p : α → β → Bool} (h : m.WF) :
    m.any p = true ↔ ∃ (a : α), a ∈ m ∧ p (m.getKeyV a) (m｢a｣)

theorem any_eq_true_iff_exists_mem_getElemV [LawfulBEq α]
    [Nonempty β] {p : α → β → Bool} (h : m.WF) :
    m.any p = true ↔ ∃ (a : α), a ∈ m ∧ p a (m｢a｣)

theorem any_eq_false_iff_forall_mem_getKeyV_getElemV [LawfulHashable α] [EquivBEq α]
    [Nonempty β] {p : α → β → Bool} (h : m.WF) :
    m.any p = false ↔ ∀ (a : α), a ∈ m → p (m.getKeyV a) (m｢a｣) = false

theorem any_eq_false_iff_forall_mem_getElemV [LawfulBEq α]
    [Nonempty β] {p : α → β → Bool} (h : m.WF) :
    m.any p = false ↔ ∀ (a : α), a ∈ m → p a (m｢a｣) = false

theorem all_eq_true_iff_forall_mem_getKeyV_getElemV [EquivBEq α] [LawfulHashable α]
    [Nonempty β] {p : α → β → Bool} (h : m.WF) :
    m.all p = true ↔ ∀ (a : α), a ∈ m → p (m.getKeyV a) (m｢a｣)

theorem all_eq_true_iff_forall_mem_getElemV [LawfulBEq α]
    [Nonempty β] {p : α → β → Bool} (h : m.WF) :
    m.all p = true ↔ ∀ (a : α), a ∈ m → p a (m｢a｣)

theorem all_eq_false_iff_exists_mem_getKeyV_getElemV [EquivBEq α] [LawfulHashable α]
    [Nonempty β] {p : α → β → Bool} (h : m.WF) :
    m.all p = false ↔ ∃ (a : α), a ∈ m ∧ p (m.getKeyV a) (m｢a｣) = false

theorem all_eq_false_iff_exists_mem_getElemV [LawfulBEq α]
    [Nonempty β] {p : α → β → Bool} (h : m.WF) :
    m.all p = false ↔ ∃ (a : α), a ∈ m ∧ p a (m｢a｣) = false
```

### HashSet/RawLemmas.lean (1)

```lean
-- Counterpart: all_eq_false_iff_exists_mem_getElem [LawfulBEq α] {p : α → Bool} (h : m.WF) :
--   m.all p = false ↔ ∃ (a : α), a ∈ m ∧ p a = false
-- Note: the set version already has `p a` not `p a (m[a]'h)`, and getV is for keys.
-- This V variant replaces the `get` in `all_eq_false_iff_exists_mem_get`:
-- Counterpart: all_eq_false_iff_exists_mem_get [EquivBEq α] [LawfulHashable α]
--   {p : α → Bool} (h : m.WF) :
--   m.all p = false ↔ ∃ (a : α) (h : a ∈ m), p (m.get a h) = false
theorem all_eq_false_iff_exists_mem_getV [EquivBEq α] [LawfulHashable α]
    [Nonempty α] {p : α → Bool} (h : m.WF) :
    m.all p = false ↔ ∃ (a : α), a ∈ m ∧ p (m.getV a) = false
```

## Part C: get/getKey V variants (~50+ lemmas)

These cover `get` (with membership proof) -> `getV` and `getKey` (with membership proof) -> `getKeyV`.

### TreeMap/Lemmas.lean (~6)

```lean
-- Counterpart: get_eq_getElem {a : α} {h} : get t a h = t[a]'h
theorem getV_eq_getElemV [TransCmp cmp] {_ : Nonempty β} {a : α} :
    getV t a = t｢a｣

-- Counterpart: getKey_insert [TransCmp cmp] {k a : α} {v : β} {h₁} :
--   (t.insert k v).getKey a h₁ =
--     if h₂ : cmp k a = .eq then k else t.getKey a (mem_of_mem_insert h₁ h₂)
theorem getKeyV_insert [TransCmp cmp] {_ : Nonempty α} {k a : α} {v : β} :
    (t.insert k v).getKeyV a =
      if cmp k a = .eq then k else t.getKeyV a

-- Counterpart: getKey_erase [TransCmp cmp] {k a : α} {h'} :
--   (t.erase k).getKey a h' = t.getKey a (mem_of_mem_erase h')
theorem getKeyV_erase [TransCmp cmp] {_ : Nonempty α} {k a : α} :
    (t.erase k).getKeyV a = t.getKeyV a

-- Counterpart: getKey_insertIfNew [TransCmp cmp] {k a : α} {v : β} {h₁} :
--   (t.insertIfNew k v).getKey a h₁ =
--     if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then k
--     else t.getKey a (mem_of_mem_insertIfNew' h₁ h₂)
theorem getKeyV_insertIfNew [TransCmp cmp] {_ : Nonempty α} {k a : α} {v : β} :
    (t.insertIfNew k v).getKeyV a =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKeyV a

-- Counterpart: get_getKey? [TransCmp cmp] {a : α} {h} :
--   (t.getKey? a).get h = t.getKey a (mem_iff_isSome_getKey?.mpr h)
-- V variant relates getV (of Option) to getKeyV:
theorem getV_getKey? [TransCmp cmp] {_ : Nonempty α} {a : α} {h : (t.getKey? a).isSome} :
    (t.getKey? a).getV = t.getKeyV a

-- Counterpart: get_eq_getElem {a : α} {h} : get t a h = t[a]'h (relates get and getElem)
-- V variant relates getElemV and getV:
theorem getElemV_eq_getV [TransCmp cmp] {_ : Nonempty β} {a : α} :
    t｢a｣ = getV t a
```

### TreeMap/Raw/Lemmas.lean (~6)

Same as TreeMap/Lemmas.lean, with `(h : t.WF)` added:

```lean
theorem getV_eq_getElemV [TransCmp cmp] {_ : Nonempty β} (h : t.WF) {a : α} :
    getV t a = t｢a｣

theorem getKeyV_insert [TransCmp cmp] {_ : Nonempty α} (h : t.WF) {k a : α} {v : β} :
    (t.insert k v).getKeyV a =
      if cmp k a = .eq then k else t.getKeyV a

theorem getKeyV_erase [TransCmp cmp] {_ : Nonempty α} (h : t.WF) {k a : α} :
    (t.erase k).getKeyV a = t.getKeyV a

theorem getKeyV_insertIfNew [TransCmp cmp] {_ : Nonempty α} (h : t.WF) {k a : α} {v : β} :
    (t.insertIfNew k v).getKeyV a =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKeyV a

theorem getV_getKey? [TransCmp cmp] {_ : Nonempty α} (h : t.WF)
    {a : α} {h' : (t.getKey? a).isSome} :
    (t.getKey? a).getV = t.getKeyV a

theorem getElemV_eq_getV [TransCmp cmp] {_ : Nonempty β} (h : t.WF) {a : α} :
    t｢a｣ = getV t a
```

### HashMap/Lemmas.lean (~6)

```lean
-- Counterpart: get_eq_getElem {a : α} {h} : get m a h = m[a]'h
theorem getV_eq_getElemV [EquivBEq α] [LawfulHashable α] {_ : Nonempty β} {a : α} :
    getV m a = m｢a｣

-- Counterpart: getKey_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁} :
--   (m.insert k v).getKey a h₁ =
--     if h₂ : k == a then k else m.getKey a (mem_of_mem_insert h₁ (by simpa using h₂))
theorem getKeyV_insert [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} {k a : α} {v : β} :
    (m.insert k v).getKeyV a =
      if k == a then k else m.getKeyV a

-- Counterpart: getKey_erase [EquivBEq α] [LawfulHashable α] {k a : α} {h'} :
--   (m.erase k).getKey a h' = m.getKey a (mem_of_mem_erase h')
theorem getKeyV_erase [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} {k a : α} :
    (m.erase k).getKeyV a = m.getKeyV a

-- Counterpart: getKey_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁} :
--   getKey (m.insertIfNew k v) a h₁ =
--     if h₂ : k == a ∧ ¬k ∈ m then k else getKey m a (mem_of_mem_insertIfNew' h₁ h₂)
theorem getKeyV_insertIfNew [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} {k a : α} {v : β} :
    (m.insertIfNew k v).getKeyV a =
      if k == a ∧ ¬k ∈ m then k else m.getKeyV a

-- Counterpart: get_getKey? [EquivBEq α] [LawfulHashable α] {a : α} {h} :
--   (m.getKey? a).get h = m.getKey a (mem_iff_isSome_getKey?.mpr h)
theorem getV_getKey? [EquivBEq α] [LawfulHashable α] {_ : Nonempty α}
    {a : α} {h : (m.getKey? a).isSome} :
    (m.getKey? a).getV = m.getKeyV a

-- Counterpart: get_eq_getElem {a : α} {h} : get m a h = m[a]'h
theorem getElemV_eq_getV [EquivBEq α] [LawfulHashable α] {_ : Nonempty β} {a : α} :
    m｢a｣ = getV m a
```

### HashMap/RawLemmas.lean (~7)

Same as HashMap/Lemmas.lean with `(h : m.WF)`:

```lean
theorem getV_eq_getElemV [EquivBEq α] [LawfulHashable α] {_ : Nonempty β}
    (h : m.WF) {a : α} :
    getV m a = m｢a｣

theorem getKeyV_insert [EquivBEq α] [LawfulHashable α] {_ : Nonempty α}
    (h : m.WF) {k a : α} {v : β} :
    (m.insert k v).getKeyV a =
      if k == a then k else m.getKeyV a

theorem getKeyV_erase [EquivBEq α] [LawfulHashable α] {_ : Nonempty α}
    (h : m.WF) {k a : α} :
    (m.erase k).getKeyV a = m.getKeyV a

theorem getKeyV_insertIfNew [EquivBEq α] [LawfulHashable α] {_ : Nonempty α}
    (h : m.WF) {k a : α} {v : β} :
    (m.insertIfNew k v).getKeyV a =
      if k == a ∧ ¬k ∈ m then k else m.getKeyV a

theorem getV_getKey? [EquivBEq α] [LawfulHashable α] {_ : Nonempty α}
    (h : m.WF) {a : α} {h' : (m.getKey? a).isSome} :
    (m.getKey? a).getV = m.getKeyV a

theorem getElemV_eq_getV [EquivBEq α] [LawfulHashable α] {_ : Nonempty β}
    (h : m.WF) {a : α} :
    m｢a｣ = getV m a
```

### ExtHashMap/Lemmas.lean (~3)

```lean
-- Counterpart: get_eq_getElem [EquivBEq α] [LawfulHashable α] {a : α} {h} :
--   get m a h = m[a]'h
theorem getV_eq_getElemV [EquivBEq α] [LawfulHashable α] {_ : Nonempty β} {a : α} :
    getV m a = m｢a｣

-- Counterpart: getKey_erase [EquivBEq α] [LawfulHashable α] {k a : α} {h'} :
--   (m.erase k).getKey a h' = m.getKey a (mem_of_mem_erase h')
theorem getKeyV_erase [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} {k a : α} :
    (m.erase k).getKeyV a = m.getKeyV a

-- Counterpart: get_getKey? [EquivBEq α] [LawfulHashable α] {a : α} {h} :
--   (m.getKey? a).get h = m.getKey a (mem_iff_isSome_getKey?.mpr h)
theorem getV_getKey? [EquivBEq α] [LawfulHashable α] {_ : Nonempty α}
    {a : α} {h : (m.getKey? a).isSome} :
    (m.getKey? a).getV = m.getKeyV a
```

### ExtTreeMap/Lemmas.lean (~5)

```lean
-- Counterpart: get_eq_getElem [TransCmp cmp] {a : α} {h} : get t a h = t[a]'h
theorem getV_eq_getElemV [TransCmp cmp] {_ : Nonempty β} {a : α} :
    getV t a = t｢a｣

-- Counterpart: getKey_insert [TransCmp cmp] {k a : α} {v : β} {h₁} :
--   (t.insert k v).getKey a h₁ =
--     if h₂ : cmp k a = .eq then k else t.getKey a (mem_of_mem_insert h₁ h₂)
theorem getKeyV_insert [TransCmp cmp] {_ : Nonempty α} {k a : α} {v : β} :
    (t.insert k v).getKeyV a =
      if cmp k a = .eq then k else t.getKeyV a

-- Counterpart: getKey_erase [TransCmp cmp] {k a : α} {h'} :
--   (t.erase k).getKey a h' = t.getKey a (mem_of_mem_erase h')
theorem getKeyV_erase [TransCmp cmp] {_ : Nonempty α} {k a : α} :
    (t.erase k).getKeyV a = t.getKeyV a

-- Counterpart: getKey_insertIfNew [TransCmp cmp] {k a : α} {v : β} {h₁} :
--   (t.insertIfNew k v).getKey a h₁ =
--     if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then k
--     else t.getKey a (mem_of_mem_insertIfNew' h₁ h₂)
theorem getKeyV_insertIfNew [TransCmp cmp] {_ : Nonempty α} {k a : α} {v : β} :
    (t.insertIfNew k v).getKeyV a =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKeyV a

-- Counterpart: get_getKey? [TransCmp cmp] {a : α} {h} :
--   (t.getKey? a).get h = t.getKey a (mem_iff_isSome_getKey?.mpr h)
theorem getV_getKey? [TransCmp cmp] {_ : Nonempty α}
    {a : α} {h : (t.getKey? a).isSome} :
    (t.getKey? a).getV = t.getKeyV a
```

### DTreeMap/Lemmas.lean (~7)

DTreeMap has both dependent `get` and `Const.get`. V variants use `getV` (not `getElemV`).

```lean
-- In root namespace (dependent):

-- Counterpart: get_insert [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} {v : β k} {h₁} :
--   (t.insert k v).get a h₁ =
--     if h₂ : cmp k a = .eq then cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp h₂)) v
--     else t.get a (mem_of_mem_insert h₁ h₂)
theorem getV_insert [TransCmp cmp] [LawfulEqCmp cmp] {_ : Nonempty (β a)} {k a : α} {v : β k} :
    (t.insert k v).getV a =
      if h₂ : cmp k a = .eq then cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp h₂)) v
      else t.getV a

-- Counterpart: get_erase [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} {h'} :
--   (t.erase k).get a h' = t.get a (mem_of_mem_erase h')
theorem getV_erase [TransCmp cmp] [LawfulEqCmp cmp] {_ : Nonempty (β a)} {k a : α} :
    (t.erase k).getV a = t.getV a

-- Counterpart: getKey_insert [TransCmp cmp] {k a : α} {v : β k} {h₁} :
--   (t.insert k v).getKey a h₁ =
--     if h₂ : cmp k a = .eq then k else t.getKey a (mem_of_mem_insert h₁ h₂)
theorem getKeyV_insert [TransCmp cmp] {_ : Nonempty α} {k a : α} {v : β k} :
    (t.insert k v).getKeyV a =
      if cmp k a = .eq then k else t.getKeyV a

-- Counterpart: getKey_erase [TransCmp cmp] {k a : α} {h'} :
--   (t.erase k).getKey a h' = t.getKey a (mem_of_mem_erase h')
theorem getKeyV_erase [TransCmp cmp] {_ : Nonempty α} {k a : α} :
    (t.erase k).getKeyV a = t.getKeyV a

-- Counterpart: get_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] {k a : α} {v : β k} {h₁} :
--   (t.insertIfNew k v).get a h₁ =
--     if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then cast ... v
--     else t.get a (mem_of_mem_insertIfNew' h₁ h₂)
theorem getV_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] {_ : Nonempty (β a)}
    {k a : α} {v : β k} :
    (t.insertIfNew k v).getV a =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp h₂.1)) v
      else t.getV a

-- Counterpart: getKey_insertIfNew [TransCmp cmp] {k a : α} {v : β k} {h₁} :
--   similar to getKey_insert but with ¬ k ∈ t condition
theorem getKeyV_insertIfNew [TransCmp cmp] {_ : Nonempty α} {k a : α} {v : β k} :
    (t.insertIfNew k v).getKeyV a =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKeyV a

-- In Const namespace:

-- Counterpart: Const.get_eq_get [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {h} :
--   get t a h = t.get a h
-- V variant relates Const.getV to the dependent getV:
theorem Const.getV_eq_getV [TransCmp cmp] [LawfulEqCmp cmp] {_ : Nonempty β} {a : α} :
    Const.getV t a = t.getV a
```

### DTreeMap/Raw/Lemmas.lean (~7)

Same as DTreeMap/Lemmas.lean with `(h : t.WF)`:

```lean
theorem getV_insert [TransCmp cmp] [LawfulEqCmp cmp] {_ : Nonempty (β a)}
    (h : t.WF) {k a : α} {v : β k} :
    (t.insert k v).getV a =
      if h₂ : cmp k a = .eq then cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp h₂)) v
      else t.getV a

theorem getV_erase [TransCmp cmp] [LawfulEqCmp cmp] {_ : Nonempty (β a)}
    (h : t.WF) {k a : α} :
    (t.erase k).getV a = t.getV a

theorem getKeyV_insert [TransCmp cmp] {_ : Nonempty α}
    (h : t.WF) {k a : α} {v : β k} :
    (t.insert k v).getKeyV a =
      if cmp k a = .eq then k else t.getKeyV a

theorem getKeyV_erase [TransCmp cmp] {_ : Nonempty α}
    (h : t.WF) {k a : α} :
    (t.erase k).getKeyV a = t.getKeyV a

theorem getV_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] {_ : Nonempty (β a)}
    (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v).getV a =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp h₂.1)) v
      else t.getV a

theorem getKeyV_insertIfNew [TransCmp cmp] {_ : Nonempty α}
    (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v).getKeyV a =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKeyV a

-- Const namespace:
theorem Const.getV_eq_getV [TransCmp cmp] [LawfulEqCmp cmp] {_ : Nonempty β}
    (h : t.WF) {a : α} :
    Const.getV t a = t.getV a
```

### DHashMap/Lemmas.lean (~6)

```lean
-- In root namespace (dependent):

-- Counterpart: get_insert [LawfulBEq α] {k a : α} {v : β k} {h₁} :
--   (m.insert k v).get a h₁ =
--     if h₂ : k == a then cast (congrArg β (eq_of_beq h₂)) v
--     else m.get a (mem_of_mem_insert h₁ (Bool.eq_false_iff.2 h₂))
theorem getV_insert [LawfulBEq α] {_ : Nonempty (β a)} {k a : α} {v : β k} :
    (m.insert k v).getV a =
      if h₂ : k == a then cast (congrArg β (eq_of_beq h₂)) v
      else m.getV a

-- Counterpart: get_erase [LawfulBEq α] {k a : α} {h'} :
--   (m.erase k).get a h' = m.get a (mem_of_mem_erase h')
theorem getV_erase [LawfulBEq α] {_ : Nonempty (β a)} {k a : α} :
    (m.erase k).getV a = m.getV a

-- Counterpart: getKey_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β k} {h₁} :
--   (m.insert k v).getKey a h₁ =
--     if h₂ : k == a then k else m.getKey a (...)
theorem getKeyV_insert [EquivBEq α] [LawfulHashable α] {_ : Nonempty α}
    {k a : α} {v : β k} :
    (m.insert k v).getKeyV a =
      if k == a then k else m.getKeyV a

-- Counterpart: getKey_erase [EquivBEq α] [LawfulHashable α] {k a : α} {h'} :
--   (m.erase k).getKey a h' = m.getKey a (mem_of_mem_erase h')
theorem getKeyV_erase [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} {k a : α} :
    (m.erase k).getKeyV a = m.getKeyV a

-- Counterpart: get_insertIfNew [LawfulBEq α] {k a : α} {v : β k} {h₁} :
--   (m.insertIfNew k v).get a h₁ =
--     if h₂ : k == a ∧ ¬k ∈ m then cast ... v
--     else m.get a (mem_of_mem_insertIfNew' h₁ h₂)
theorem getV_insertIfNew [LawfulBEq α] {_ : Nonempty (β a)} {k a : α} {v : β k} :
    (m.insertIfNew k v).getV a =
      if h₂ : k == a ∧ ¬k ∈ m then cast (congrArg β (eq_of_beq h₂.1)) v
      else m.getV a

-- In Const namespace:

-- Counterpart: Const.get_eq_get [LawfulBEq α] {a : α} {h} : get m a h = m.get a h
theorem Const.getV_eq_getV [LawfulBEq α] {_ : Nonempty β} {a : α} :
    Const.getV m a = m.getV a
```

### DHashMap/RawLemmas.lean (~6)

Same as DHashMap/Lemmas.lean with `(h : m.WF)`:

```lean
theorem getV_insert [LawfulBEq α] {_ : Nonempty (β a)}
    (h : m.WF) {k a : α} {v : β k} :
    (m.insert k v).getV a =
      if h₂ : k == a then cast (congrArg β (eq_of_beq h₂)) v
      else m.getV a

theorem getV_erase [LawfulBEq α] {_ : Nonempty (β a)}
    (h : m.WF) {k a : α} :
    (m.erase k).getV a = m.getV a

theorem getKeyV_insert [EquivBEq α] [LawfulHashable α] {_ : Nonempty α}
    (h : m.WF) {k a : α} {v : β k} :
    (m.insert k v).getKeyV a =
      if k == a then k else m.getKeyV a

theorem getKeyV_erase [EquivBEq α] [LawfulHashable α] {_ : Nonempty α}
    (h : m.WF) {k a : α} :
    (m.erase k).getKeyV a = m.getKeyV a

theorem getV_insertIfNew [LawfulBEq α] {_ : Nonempty (β a)}
    (h : m.WF) {k a : α} {v : β k} :
    (m.insertIfNew k v).getV a =
      if h₂ : k == a ∧ ¬k ∈ m then cast (congrArg β (eq_of_beq h₂.1)) v
      else m.getV a

-- Const namespace:
theorem Const.getV_eq_getV [LawfulBEq α] {_ : Nonempty β}
    (h : m.WF) {a : α} :
    Const.getV m a = m.getV a
```

### TreeSet/Lemmas.lean (~4)

For sets, `get` takes a membership proof and returns the canonical key.
`getV` replaces this with a `Nonempty α` instance.

```lean
-- Counterpart: get_insert [TransCmp cmp] {k a : α} {h₁} :
--   (t.insert k).get a h₁ =
--     if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then k
--     else t.get a (mem_of_mem_insert' h₁ h₂)
theorem getV_insert [TransCmp cmp] {_ : Nonempty α} {k a : α} :
    (t.insert k).getV a =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getV a

-- Counterpart: get_erase [TransCmp cmp] {k a : α} {h'} :
--   (t.erase k).get a h' = t.get a (mem_of_mem_erase h')
theorem getV_erase [TransCmp cmp] {_ : Nonempty α} {k a : α} :
    (t.erase k).getV a = t.getV a

-- Counterpart: get_get? [TransCmp cmp] {k : α} {h} :
--   (t.get? k).get h = t.get k (mem_iff_isSome_get?.mpr h)
theorem getV_get? [TransCmp cmp] {_ : Nonempty α} {k : α} {h : (t.get? k).isSome} :
    (t.get? k).getV = t.getV k

-- Counterpart: min_eq_getElem_toArray [TransCmp cmp] {he} :
--   t.min he = t.toArray[0]'(...)
theorem minV_eq_getElemV_toArray [TransCmp cmp] {_ : Nonempty α} :
    t.minV = t.toArray[0]ᵥ
```

### TreeSet/Raw/Lemmas.lean (~3)

```lean
theorem getV_insert [TransCmp cmp] {_ : Nonempty α} (h : t.WF) {k a : α} :
    (t.insert k).getV a =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getV a

theorem getV_erase [TransCmp cmp] {_ : Nonempty α} (h : t.WF) {k a : α} :
    (t.erase k).getV a = t.getV a

theorem getV_get? [TransCmp cmp] {_ : Nonempty α} (h : t.WF)
    {k : α} {h' : (t.get? k).isSome} :
    (t.get? k).getV = t.getV k
```

Note: TreeSet.Raw does not have `min_eq_getElem_toArray`, so no `minV_eq_getElemV_toArray` needed.

### HashSet/Lemmas.lean (~3)

```lean
-- Counterpart: get_insert [EquivBEq α] [LawfulHashable α] {k a : α} {h₁} :
--   (m.insert k).get a h₁ =
--     if h₂ : k == a ∧ ¬k ∈ m then k else m.get a (mem_of_mem_insert' h₁ h₂)
theorem getV_insert [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} {k a : α} :
    (m.insert k).getV a =
      if k == a ∧ ¬k ∈ m then k else m.getV a

-- Counterpart: get_erase [EquivBEq α] [LawfulHashable α] {k a : α} {h'} :
--   (m.erase k).get a h' = m.get a (mem_of_mem_erase h')
theorem getV_erase [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} {k a : α} :
    (m.erase k).getV a = m.getV a

-- Counterpart: get_get? [EquivBEq α] [LawfulHashable α] {k : α} {h} :
--   (m.get? k).get h = m.get k (mem_iff_isSome_get?.mpr h)
theorem getV_get? [EquivBEq α] [LawfulHashable α] {_ : Nonempty α}
    {k : α} {h : (m.get? k).isSome} :
    (m.get? k).getV = m.getV k
```

### HashSet/RawLemmas.lean (~3)

```lean
theorem getV_insert [EquivBEq α] [LawfulHashable α] {_ : Nonempty α}
    (h : m.WF) {k a : α} :
    (m.insert k).getV a =
      if k == a ∧ ¬k ∈ m then k else m.getV a

theorem getV_erase [EquivBEq α] [LawfulHashable α] {_ : Nonempty α}
    (h : m.WF) {k a : α} :
    (m.erase k).getV a = m.getV a

theorem getV_get? [EquivBEq α] [LawfulHashable α] {_ : Nonempty α}
    (h : m.WF) {k : α} {h' : (m.get? k).isSome} :
    (m.get? k).getV = m.getV k
```

## Notes

- For map types (TreeMap, HashMap, ExtHashMap, ExtTreeMap), V variants use `{_ : Nonempty β}`
  (or `haveI` when witness available). Per SIGNATURE_SPEC, use `{_ :}` not `[Nonempty β]`.
  (Step 3d will clean up existing `[Nonempty β]` usage.)
- For DTreeMap/DHashMap, V variants use `getV` not `getElemV` (dependent types).
- For set types, `getV` replaces `get` which takes membership proof.
- `any_*/all_*` V variants: Replace `m[a]'h` with `m｢a｣` and `m.getKey a h` with `m.getKeyV a`
  inside the quantifier. The membership condition moves from a dependent binder `(h : a ∈ m)`
  to a simple `a ∈ m ∧ ...` or `a ∈ m → ...` since V operations don't need the proof.
- For `getKeyV_insert` and `getKeyV_erase`: the membership proof in the if-condition drops to
  a simple boolean condition, and the fallback branch returns `getKeyV` (which returns
  `Classical.ofNonempty` when not found, matching both sides).
- `getV_getV` / `Const.getV_eq_getV`: relates `Const.getV` to the dependent-type `getV`.
- Items 10, 13 from original Part A (`getElemV_eq` for ExtHashMap/ExtTreeMap) correctly removed:
  these types don't have map equivalence (`~m`), so no `getElem_eq` counterpart exists.
- Item 11 (`getKeyV_eq`) was INCORRECTLY removed: `getKey_eq` DOES exist in both ExtHashMap
  (line 540) and ExtTreeMap (line 567). These need V variants. Added to Part C.
- Items 3-5, 8-9 from original Part A already exist in source.

## Revised Totals

- Part A: 5 new lemmas (3 `getElemV_union_of_mem_right` + 1 `getElemV_filterMap'` for ExtHashMap + corrections)
- Part B: 17 new lemmas (8 + 8 + 1)
- Part C: ~54 new lemmas across all types
- **Grand total: ~76 new V variant lemmas**
