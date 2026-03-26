# Step 3e.5: ByteArray V Lemma Parity

Status: not started; Refinement Needed: no

## File

`src/Init/Data/ByteArray/Lemmas.lean`

## Prerequisite

A `GetElemV ByteArray Nat UInt8` instance and `Nonempty UInt8` instance must be added
before these lemmas can compile. These will error until then — create the lemmas anyway
so they are ready when the instances are added.

## ACTIONABLE GAPS — V variants to create

| # | V lemma | Counterpart | Annotation |
|---|---------|-------------|------------|
| 1 | `getElemV_eq_getElemV_data` | `getElem_eq_getElem_data` (line 107) | none |
| 2 | `getElemV_append_left` | `getElem_append_left` (line 111) | `@[simp]` |
| 3 | `getElemV_append_right` | `getElem_append_right` (line 116) | none |
| 4 | `getElemV_extract` | `getElem_extract` (line 224) | none |

## Total: 4 new V variant lemmas
