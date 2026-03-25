# Step 2.4: DTreeMap/Raw/Lemmas.lean — getKeyV annotations (3 annotate)

Status: not started

## File

`src/Std/Data/DTreeMap/Raw/Lemmas.lean`

## Context

Three `getKeyV_*` lemmas exist but lack the `@[grind =]` annotation that their `getKeyD_*`
counterparts have. The fix is to add `@[grind =]` to each.

## Lemmas to annotate

| # | V lemma | Counterpart (with annotation) | Required annotation | Current line | Existing signature |
|---|---------|-------------------------------|--------------------|--------------|--------------------|
| 1 | `getKeyV_insert` | `getKeyD_insert` (`@[grind =]`, line 1038) | `@[grind =]` | 1042 | `theorem getKeyV_insert [TransCmp cmp] {_ : Nonempty α} (h : t.WF) {k a : α} {v : β k} : (t.insert k v).getKeyV a = if cmp k a = .eq then k else t.getKeyV a` |
| 2 | `getKeyV_erase` | `getKeyD_erase` (`@[grind =]`, line 1071) | `@[grind =]` | 1076 | `theorem getKeyV_erase [TransCmp cmp] {_ : Nonempty α} (h : t.WF) {k a : α} : (t.erase k).getKeyV a = if cmp k a = .eq then Classical.ofNonempty else t.getKeyV a` |
| 3 | `getKeyV_insertIfNew` | `getKeyD_insertIfNew` (`@[grind =]`, line 1291) | `@[grind =]` | 1297 | `theorem getKeyV_insertIfNew [TransCmp cmp] {_ : Nonempty α} (h : t.WF) {k a : α} {v : β k} : (t.insertIfNew k v).getKeyV a = if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKeyV a` |

## Implementation

For each lemma, add `@[grind =]` before the `theorem` keyword:

1. Line 1042: change `theorem getKeyV_insert` to `@[grind =] theorem getKeyV_insert`
2. Line 1076: change `theorem getKeyV_erase` to `@[grind =] theorem getKeyV_erase`
3. Line 1297: change `theorem getKeyV_insertIfNew` to `@[grind =] theorem getKeyV_insertIfNew`

No signature changes needed. Only the annotation is added.
