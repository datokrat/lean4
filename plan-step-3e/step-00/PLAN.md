# Step 3e.0: GetElem.lean Generic V Lemmas

Status: not started; Refinement Needed: no

## File

`src/Init/GetElem.lean`

## Goal

Add V variants for the generic getElem infrastructure lemmas. These are polymorphic over
all collection types and relate `getElem`/`getElem?`/`getElem!` to each other.

## ACTIONABLE GAPS — V variants to create

| # | V lemma | Counterpart | Annotation | Suggested signature |
|---|---------|-------------|------------|---------------------|
| 1 | `getElemV_congr` | `getElem_congr` (line 143) | `@[simp, grind]` | `theorem getElemV_congr [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom] [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom] {_ : Nonempty elem} {c d : cont} {i j : idx} (h₁ : c = d) (h₂ : i = j) : c｢i｣ = d｢j｣` |
| 2 | `getElemV_congr_coll` | `getElem_congr_coll` (line 147) | none | `theorem getElemV_congr_coll [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom] [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom] {_ : Nonempty elem} {c d : cont} {i : idx} (h : c = d) : c｢i｣ = d｢i｣` |
| 3 | `getElemV_congr_idx` | `getElem_congr_idx` (line 151) | none | `theorem getElemV_congr_idx [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom] [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom] {_ : Nonempty elem} {c : cont} {i j : idx} (h : i = j) : c｢i｣ = c｢j｣` |
| 4 | `getElem?_pos_getElemV` | `getElem?_pos` (line 187) | none | `theorem getElem?_pos_getElemV [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom] [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom] (c : cont) (i : idx) (h : dom c i) : haveI : Nonempty elem := ⟨c[i]⟩; c[i]? = some c｢i｣` |
| 5 | `getElem!_pos_getElemV` | `getElem!_pos` (line 221) | none | `theorem getElem!_pos_getElemV [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom] [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom] [Inhabited elem] (c : cont) (i : idx) (h : dom c i) : c[i]! = c｢i｣` |
| 6 | `get_getElem?_getElemV` | `get_getElem?` (line 245) | `@[simp, grind =]` | `theorem get_getElem?_getElemV [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom] [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom] (c : cont) (i : idx) [Decidable (dom c i)] (h : (c[i]?).isSome) : haveI : Nonempty elem := ⟨(c[i]?).get h⟩; (c[i]?).get h = c｢i｣` |
| 7 | `getElem?_eq_some_iff_getElemV` | `getElem?_eq_some_iff` (line 270) | none | `theorem getElem?_eq_some_iff_getElemV [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom] [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom] {c : cont} {i : idx} [Decidable (dom c i)] {a : elem} : c[i]? = some a ↔ ∃ h : dom c i, c｢i｣ = a` |
| 8 | `some_eq_getElem?_iff_getElemV` | `some_eq_getElem?_iff` (line 288) | none | `theorem some_eq_getElem?_iff_getElemV [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom] [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom] {c : cont} {i : idx} [Decidable (dom c i)] {a : elem} : some a = c[i]? ↔ ∃ h : dom c i, c｢i｣ = a` |
| 9 | `getElemV_of_getElem?` | `getElem_of_getElem?` (line 292) | none | `theorem getElemV_of_getElem? [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom] [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom] {c : cont} {i : idx} [Decidable (dom c i)] {a : elem} (h : c[i]? = some a) : haveI : Nonempty elem := ⟨a⟩; c｢i｣ = a` |
| 10 | `of_getElemV_eq` | `of_getElem_eq` (line 296) | none | `theorem of_getElemV_eq [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom] [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom] {c : cont} {i : idx} [Decidable (dom c i)] {_ : Nonempty elem} (h₁ : dom c i) (h₂ : c｢i｣ = a) : c[i]? = some a` |
| 11 | `some_getElemV_eq_getElem?_iff` | `some_getElem_eq_getElem?_iff` (line 299) | `@[simp]` | `theorem some_getElemV_eq_getElem?_iff [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom] [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom] {c : cont} {i : idx} [Decidable (dom c i)] (h : dom c i) : haveI : Nonempty elem := ⟨c[i]⟩; (some c｢i｣ = c[i]?) ↔ True` |
| 12 | `getElem?_eq_some_getElemV_iff` | `getElem?_eq_some_getElem_iff` (line 304) | `@[simp]` | `theorem getElem?_eq_some_getElemV_iff [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom] [GetElemV cont idx elem] [LawfulGetElemV cont idx elem dom] {c : cont} {i : idx} [Decidable (dom c i)] (h : dom c i) : haveI : Nonempty elem := ⟨c[i]⟩; (c[i]? = some c｢i｣) ↔ True` |

## Notes

- These are generic lemmas parameterized over `GetElem cont idx elem dom` / `GetElemV cont idx elem`.
  The V variants use `getElemV` (`｢i｣`) notation on the LHS/RHS.
- `getElem?` and `getElem!` do NOT have V forms themselves. Items 4-6 bridge `getElem?`/`getElem!`
  with `getElemV` — the `?`/`!` side stays as-is, only the proof-taking `c[i]'h` is replaced by `c｢i｣`.
- Items 7-10 are iff/extraction lemmas. The V variant replaces the proof-taking `c[i]'h` form with `c｢i｣`.
- Items 11-12 are simp lemmas that simplify `some c｢i｣ = c[i]?` to `True`.
- Note: `getElem?_eq_some_getElemV` (line 202) and `getElem_eq_getElemV` (line 194) already exist
  in the source file and do not need to be added.
- Where a `Nonempty elem` witness is available from context (e.g., `c[i]` when `dom c i` holds, or
  an element `a` from a `some a` hypothesis), we use `haveI : Nonempty elem := ⟨witness⟩` per
  SIGNATURE_SPEC.md. Where no witness is available, we use `{_ : Nonempty elem}`.
- Proofs: most follow from `simp [getElem_eq_getElemV]` or `simp [getElemV_pos h]` combined with
  the corresponding non-V lemma.
- `getElem?_eq_getElem` (line 401, `@[local simp]`) contains proof-taking `l[i]` on the RHS.
  V variant replaces with `l｢i｣`. Note: this is List-specific (not generic over `GetElem`).
- `getInternal_eq_getElem` (line 504, `@[simp]`) contains proof-taking `a[i]` on the RHS.
  V variant replaces with `a｢i｣`. Note: this is Array-specific.

### Additional lemmas (2)

| # | V lemma | Counterpart | Annotation | Suggested signature |
|---|---------|-------------|------------|---------------------|
| 13 | `getElem?_eq_getElemV` | `getElem?_eq_getElem` (line 401) | `@[local simp]` | `@[local simp] theorem getElem?_eq_getElemV {l : List α} {i} (h : i < l.length) : haveI : Nonempty α := ⟨l[i]⟩; l[i]? = some l｢i｣` |
| 14 | `getInternal_eq_getElemV` | `getInternal_eq_getElem` (line 504) | `@[simp]` | `@[simp] theorem getInternal_eq_getElemV (a : Array α) (i : Nat) (h) : haveI : Nonempty α := ⟨a.getInternal i h⟩; a.getInternal i h = a｢i｣` |

## Total: 14 new V variant lemmas
