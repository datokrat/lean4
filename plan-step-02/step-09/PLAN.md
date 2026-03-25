# Step 2.9: Ext types — annotation-only across 4 files

Status: not started

## Overview

All Ext type V lemmas already exist. They just need `@[grind =]` annotations to match their proof-taking counterparts (all of which have `@[grind =]`).

---

## 2.9.1 `src/Std/Data/ExtTreeMap/Lemmas.lean` (3 annotate)

| V lemma | Line | Counterpart (has `@[grind =]`) | Action |
|---------|------|-------------------------------|--------|
| `getKeyV_insert` | 644 | `getKeyD_insert` (line 640) | add `@[grind =]` |
| `getKeyV_erase` | 678 | `getKeyD_erase` (line 673) | add `@[grind =]` |
| `getKeyV_insertIfNew` | 849 | `getKeyD_insertIfNew` (line 843) | add `@[grind =]` |

### Existing signatures (no changes needed, annotation only)

```lean
-- line 644
theorem getKeyV_insert [TransCmp cmp] {_ : Nonempty α} {k a : α} {v : β} :
    (t.insert k v).getKeyV a = if cmp k a = .eq then k else t.getKeyV a

-- line 678
theorem getKeyV_erase [TransCmp cmp] {_ : Nonempty α} {k a : α} :
    (t.erase k).getKeyV a = if cmp k a = .eq then Classical.ofNonempty else t.getKeyV a

-- line 849
theorem getKeyV_insertIfNew [TransCmp cmp] {_ : Nonempty α} {k a : α} {v : β} :
    (t.insertIfNew k v).getKeyV a =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKeyV a
```

---

## 2.9.2 `src/Std/Data/ExtHashMap/Lemmas.lean` (9 annotate)

| V lemma | Line | Counterpart (has `@[grind =]`) | Action |
|---------|------|-------------------------------|--------|
| `getKeyV_insert` | 614 | `getKeyD_insert` (line 610) | add `@[grind =]` |
| `getKeyV_erase` | 647 | `getKeyD_erase` (line 643) | add `@[grind =]` |
| `getKeyV_insertIfNew` | 820 | `getKeyD_insertIfNew` (line 816) | add `@[grind =]` |
| `getKeyV_alter` | 2608 | `getKeyD_alter` (line 2599) | add `@[grind =]` |
| `getElemV_modify` | 2708 | `getD_modify` (line 2695) | add `@[grind =]` |
| `getKeyV_modify` | 2767 | `getKeyD_modify` (line 2759) | add `@[grind =]` |
| `getElemV_filterMap` | 2915 | `getD_filterMap` (line 2903) | add `@[grind =]` |
| `getKeyV_filterMap` | 2954 | `getKeyD_filterMap` (line 2947) | add `@[grind =]` |
| `getKeyV_filter` | 3127 | `getKeyD_filter` (line 3120) | add `@[grind =]` |

### Existing signatures (annotation only)

```lean
-- line 614
theorem getKeyV_insert [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} {k a : α} {v : β} :
    (m.insert k v).getKeyV a = if k == a then k else m.getKeyV a

-- line 647
theorem getKeyV_erase [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} {k a : α} :
    (m.erase k).getKeyV a = if k == a then Classical.ofNonempty else m.getKeyV a

-- line 820
theorem getKeyV_insertIfNew [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} {k a : α} {v : β} :
    getKeyV (m.insertIfNew k v) a = if k == a ∧ ¬k ∈ m then k else getKeyV m a

-- line 2608
theorem getKeyV_alter [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} {k k' : α}
    {f : Option β → Option β} :
    (alter m k f).getKeyV k' = ...

-- line 2708
theorem getElemV_modify [EquivBEq α] [LawfulHashable α] {_ : Nonempty β} {k k' : α} {f : β → β} :
    (modify m k f)｢k'｣ = ...

-- line 2767
theorem getKeyV_modify [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} {k k' : α} {f : β → β} :
    (modify m k f).getKeyV k' = ...

-- line 2915
theorem getElemV_filterMap [EquivBEq α] [LawfulHashable α] {_ : Nonempty γ}
    {f : (a : α) → β → Option γ} {k : α} :
    (m.filterMap f)｢k｣ = ...

-- line 2954
theorem getKeyV_filterMap [EquivBEq α] [LawfulHashable α] {_ : Nonempty α}
    {f : (a : α) → β → Option γ} {k : α} :
    (m.filterMap f).getKeyV k = ...

-- line 3127
theorem getKeyV_filter [EquivBEq α] [LawfulHashable α] {_ : Nonempty α}
    {f : (a : α) → β → Bool} {k : α} :
    (m.filter f).getKeyV k = ...
```

---

## 2.9.3 `src/Std/Data/ExtDHashMap/Lemmas.lean` (3 annotate)

| V lemma | Line | Counterpart (has `@[grind =]`) | Action |
|---------|------|-------------------------------|--------|
| `getKeyV_insert` | 864 | `getKeyD_insert` (line 862) | add `@[grind =]` |
| `getKeyV_erase` | 900 | `getKeyD_erase` (line 898) | add `@[grind =]` |
| `getKeyV_insertIfNew` | 1107 | `getKeyD_insertIfNew` (line 1105) | add `@[grind =]` |

### Existing signatures (annotation only)

```lean
-- line 864
theorem getKeyV_insert [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} {k a : α} {v : β k} :
    (m.insert k v).getKeyV a = if k == a then k else m.getKeyV a

-- line 900
theorem getKeyV_erase [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} {k a : α} :
    (m.erase k).getKeyV a = if k == a then Classical.ofNonempty else m.getKeyV a

-- line 1107
theorem getKeyV_insertIfNew [EquivBEq α] [LawfulHashable α] {_ : Nonempty α} {k a : α} {v : β k} :
    (m.insertIfNew k v).getKeyV a = if k == a ∧ ¬k ∈ m then k else m.getKeyV a
```

---

## 2.9.4 `src/Std/Data/ExtDTreeMap/Lemmas.lean` (3 annotate)

| V lemma | Line | Counterpart (has `@[grind =]`) | Action |
|---------|------|-------------------------------|--------|
| `getKeyV_insert` | 908 | `getKeyD_insert` (line 906) | add `@[grind =]` |
| `getKeyV_erase` | 942 | `getKeyD_erase` (line 940) | add `@[grind =]` |
| `getKeyV_insertIfNew` | 1157 | `getKeyD_insertIfNew` (line 1155) | add `@[grind =]` |

### Existing signatures (annotation only)

```lean
-- line 908
theorem getKeyV_insert [TransCmp cmp] {_ : Nonempty α} {k a : α} {v : β k} :
    (t.insert k v).getKeyV a = if compare k a = .eq then k else t.getKeyV a

-- line 942
theorem getKeyV_erase [TransCmp cmp] {_ : Nonempty α} {k a : α} :
    (t.erase k).getKeyV a = if compare k a = .eq then Classical.ofNonempty else t.getKeyV a

-- line 1157
theorem getKeyV_insertIfNew [TransCmp cmp] {_ : Nonempty α} {k a : α} {v : β k} :
    (t.insertIfNew k v).getKeyV a = if compare k a = .eq ∧ ¬k ∈ t then k else t.getKeyV a
```

---

## Summary

| File | Annotates |
|------|-----------|
| ExtTreeMap/Lemmas.lean | 3 |
| ExtHashMap/Lemmas.lean | 9 |
| ExtDHashMap/Lemmas.lean | 3 |
| ExtDTreeMap/Lemmas.lean | 3 |
| **Total** | **18** |

All changes are `@[grind =]` annotation additions. No new lemmas need to be created.

ExtTreeSet and ExtHashSet are already complete — no changes needed.
