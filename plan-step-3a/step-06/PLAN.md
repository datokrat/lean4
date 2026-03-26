# Step 3a.6: ByteArray + String V Lemma Parity

Status: good; Refinement Needed: no

## Files

`src/Init/Data/ByteArray/Lemmas.lean`, `src/Init/Data/String/Decode.lean`,
`src/Init/Data/String/Lemmas/Pattern/String/Basic.lean`,
`src/Init/Data/String/Lemmas/Pattern/String/ForwardSearcher.lean`,
`src/Init/Data/String/Pattern/String.lean`

## Summary

All candidates in this step are NOT APPLICABLE. None of the containers indexed
by `getElem` in these lemmas have `GetElemV` instances, so V variants cannot be
written.

## Detailed Analysis

### `ByteArray/Lemmas.lean`

ByteArray has `GetElem ByteArray Nat UInt8` (line 74 of `ByteArray/Basic.lean`)
but **no `GetElemV ByteArray Nat UInt8` instance exists**. There is also no
`Nonempty UInt8` instance. Until both are added, V variants of ByteArray
getElem lemmas are blocked.

- `getElem_eq_getElem_data` (line 107) — NOT APPLICABLE: no `GetElemV ByteArray`
- `getElem_extract` (line 224) — NOT APPLICABLE: no `GetElemV ByteArray`
- `extract_eq_extract_iff_getElem` (line 315) — NOT APPLICABLE: no `GetElemV ByteArray`

### `String/Decode.lean` (6 lemmas)

These lemmas use `getElem` on `String.utf8EncodeChar c` (a `List UInt8`) with
literal numeric indices (0, 1, 2, 3). The proofs that the index is in bounds
are trivially dischargeable from the `utf8Size` hypothesis.

These are NOT APPLICABLE for two independent reasons:
1. The underlying container is `List UInt8`, and while `List` does have
   `GetElemV`, `UInt8` lacks a `Nonempty` instance.
2. The names are already extremely long (e.g.,
   `isInvalidContinuationByte_getElem_utf8EncodeChar_three_of_utf8Size_eq_four`).
   V variants would be impractical even if the infrastructure existed.
3. These are internal UTF-8 decoding helpers, not user-facing API.

All 6 lemmas: NOT APPLICABLE.

### `String/Lemmas/Pattern/String/Basic.lean`

- `ForwardSliceSearcher.matchesAt_iff_getElem` (line 105) — uses `getElem` on
  `ByteArray` (`.copy.toByteArray[j]`). NOT APPLICABLE: no `GetElemV ByteArray`.
- `matchesAt_iff_getElem` (line 236) — same situation, uses `pat.toByteArray[j]`
  and `s.copy.toByteArray[pos.offset.byteIdx + j]`. NOT APPLICABLE.

Note: The stub listed these as being in `String/Basic.lean`, but they are
actually in `String/Lemmas/Pattern/String/Basic.lean`.

### `String/Lemmas/Pattern/String/ForwardSearcher.lean`

- `getElem_buildTable` (line 345, `@[simp]`) — indexes into
  `Vector Nat pat.utf8ByteSize`. No `GetElemV` instance for `Vector`.
  NOT APPLICABLE.

### `String/Pattern/String.lean`

- `getElem_buildTable_le` (line 70) — indexes into the result of `buildTable`,
  which is `Vector Nat`. No `GetElemV` instance for `Vector`.
  NOT APPLICABLE.

## Conclusion

No action items for this step. All 12 candidates are blocked on missing
`GetElemV` instances for `ByteArray` and `Vector`. If those instances are added
in the future, these lemmas could be revisited.
