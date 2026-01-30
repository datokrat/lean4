/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Vector.Basic
public import Init.Data.Vector.Lemmas
public import Init.Data.Array.MinMax

namespace Vector

/-! ## Minima and maxima -/

/-! ### min -/

/--
Returns the smallest element of a non-empty vector.

Examples:
* `#v[4].min (by decide) = 4`
* `#v[1, 4, 2, 10, 6].min (by decide) = 1`
-/
public protected def min [Min α] (xs : Vector α n) (h : n ≠ 0) : α :=
  xs.toArray.min (by simpa using h)

/-! ### min? -/

/--
Returns the smallest element of the vector if it is not empty, or `none` if it is empty.

Examples:
* `#v[].min? = none`
* `#v[4].min? = some 4`
* `#v[1, 4, 2, 10, 6].min? = some 1`
-/
public protected def min? [Min α] (xs : Vector α n) : Option α :=
  xs.toArray.min?

/-! ### max -/

/--
Returns the largest element of a non-empty vector.

Examples:
* `#v[4].max (by decide) = 4`
* `#v[1, 4, 2, 10, 6].max (by decide) = 10`
-/
public protected def max [Max α] (xs : Vector α n) (h : n ≠ 0) : α :=
  xs.toArray.max (by simpa using h)

/-! ### max? -/

/--
Returns the largest element of the vector if it is not empty, or `none` if it is empty.

Examples:
* `#v[].max? = none`
* `#v[4].max? = some 4`
* `#v[1, 4, 2, 10, 6].max? = some 10`
-/
public protected def max? [Max α] (xs : Vector α n) : Option α :=
  xs.toArray.max?

/-! ### Compatibility with `Array` -/

@[simp, grind =]
public theorem _root_.Array.min_toVector [Min α] {xs : Array α} {h} :
    xs.toVector.min h = xs.min (by simpa using h) := by
  simp [Vector.min]

public theorem _root_.Array.min_eq_min_toVector [Min α] {xs : Array α} {h} :
    xs.min h = xs.toVector.min (by simpa using h) := by
  simp

@[simp, grind =]
public theorem min_toArray [Min α] {xs : Vector α n} {h} :
    xs.toArray.min h = xs.min (by simpa using h) := by
  simp [Vector.min]

public theorem min_eq_min_toArray [Min α] {xs : Vector α n} {h} :
    xs.min h = xs.toArray.min (by simpa using h) := by
  simp

@[simp, grind =]
public theorem _root_.Array.min?_toVector [Min α] {xs : Array α} :
    xs.toVector.min? = xs.min? := by
  simp [Vector.min?]

@[simp, grind =]
public theorem min?_toArray [Min α] {xs : Vector α n} :
    xs.toArray.min? = xs.min? := by
  simp [Vector.min?]

@[simp, grind =]
public theorem _root_.Array.max_toVector [Max α] {xs : Array α} {h} :
    xs.toVector.max h = xs.max (by simpa using h) := by
  simp [Vector.max]

public theorem _root_.Array.max_eq_max_toVector [Max α] {xs : Array α} {h} :
    xs.max h = xs.toVector.max (by simpa using h) := by
  simp

@[simp, grind =]
public theorem max_toArray [Max α] {xs : Vector α n} {h} :
    xs.toArray.max h = xs.max (by simpa using h) := by
  simp [Vector.max]

public theorem max_eq_max_toArray [Max α] {xs : Vector α n} {h} :
    xs.max h = xs.toArray.max (by simpa using h) := by
  simp

@[simp, grind =]
public theorem _root_.Array.max?_toVector [Max α] {xs : Array α} :
    xs.toVector.max? = xs.max? := by
  simp [Vector.max?]

@[simp, grind =]
public theorem max?_toArray [Max α] {xs : Vector α n} :
    xs.toArray.max? = xs.max? := by
  simp [Vector.max?]

/-! ### Lemmas about `min?` -/

@[simp, grind =]
public theorem min?_empty [Min α] : (#v[] : Vector α 0).min? = none :=
  (rfl)

@[simp, grind =]
public theorem min?_singleton [Min α] {x : α} : #v[x].min? = some x :=
  (rfl)

@[simp, grind =]
public theorem min?_eq_none_iff {xs : Vector α n} [Min α] : xs.min? = none ↔ n = 0 := by
  simp [Vector.min?]

@[simp, grind =]
public theorem isSome_min?_iff {xs : Vector α n} [Min α] : xs.min?.isSome ↔ n ≠ 0 := by
  simp [Vector.min?]

@[grind .]
public theorem isSome_min?_of_mem {xs : Vector α n} [Min α] {a : α} (h : a ∈ xs) :
    xs.min?.isSome := by
  rw [← min?_toArray]
  apply Array.isSome_min?_of_mem (a := a)
  simpa using h.val

public theorem isSome_min?_of_ne_zero [Min α] (xs : Vector α n) (h : n ≠ 0) : xs.min?.isSome := by
  rw [← min?_toArray]
  apply Array.isSome_min?_of_ne_empty
  simpa using h

public theorem min?_mem [Min α] [Std.MinEqOr α] (xs : Vector α n) (h : xs.min? = some a) : a ∈ xs := by
  rw [← min?_toArray] at h
  constructor
  exact Array.min?_mem xs.toArray h

public theorem le_min?_iff [Min α] [LE α] [Std.LawfulOrderInf α] :
    {xs : Vector α n} → xs.min? = some a → ∀ {x}, x ≤ a ↔ ∀ b, b ∈ xs → x ≤ b := by
  intro xs h x
  simp only [← min?_toArray] at h
  have := Array.le_min?_iff h (x := x)
  simpa using this

public theorem min?_eq_some_iff [Min α] [LE α] {xs : Vector α n} [Std.IsLinearOrder α]
    [Std.LawfulOrderMin α] : xs.min? = some a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → a ≤ b := by
  simp [Vector.min?, Array.min?_eq_some_iff]

public theorem min?_replicate [Min α] [Std.IdempotentOp (min : α → α → α)] {n : Nat} {a : α} :
    (replicate n a).min? = if n = 0 then none else some a := by
  simp [Vector.min?, replicate, Array.min?_replicate]

@[simp, grind =]
public theorem min?_replicate_of_pos [Min α] [Std.MinEqOr α] {n : Nat} {a : α} (h : 0 < n) :
    (replicate n a).min? = some a := by
  simp [min?_replicate, Nat.ne_of_gt h]

public theorem foldl_min [Min α] [Std.IdempotentOp (min : α → α → α)]
    [Std.Associative (min : α → α → α)] {xs : Vector α n} {a : α} :
    xs.foldl (init := a) min = min a (xs.min?.getD a) := by
  simp [Vector.foldl, Vector.min?, Array.foldl_min]

/-! ### Lemmas about `max?` -/

@[simp, grind =]
public theorem max?_empty [Max α] : (#v[] : Vector α 0).max? = none :=
  (rfl)

@[simp, grind =]
public theorem max?_singleton [Max α] {x : α} : #v[x].max? = some x :=
  (rfl)

@[simp, grind =]
public theorem max?_eq_none_iff {xs : Vector α n} [Max α] : xs.max? = none ↔ n = 0 := by
  simp [Vector.max?]

@[simp, grind =]
public theorem isSome_max?_iff {xs : Vector α n} [Max α] : xs.max?.isSome ↔ n ≠ 0 := by
  simp [Vector.max?]

@[grind .]
public theorem isSome_max?_of_mem {xs : Vector α n} [Max α] {a : α} (h : a ∈ xs) :
    xs.max?.isSome := by
  rw [← max?_toArray]
  apply Array.isSome_max?_of_mem (a := a)
  simpa using h.val

public theorem isSome_max?_of_ne_zero [Max α] (xs : Vector α n) (h : n ≠ 0) : xs.max?.isSome := by
  rw [← max?_toArray]
  apply Array.isSome_max?_of_ne_empty
  simpa using h

public theorem max?_mem [Max α] [Std.MaxEqOr α] (xs : Vector α n) (h : xs.max? = some a) : a ∈ xs := by
  rw [← max?_toArray] at h
  constructor
  exact Array.max?_mem xs.toArray h

public theorem max?_le_iff [Max α] [LE α] [Std.LawfulOrderSup α] :
    {xs : Vector α n} → xs.max? = some a → ∀ {x}, a ≤ x ↔ ∀ b, b ∈ xs → b ≤ x := by
  intro xs h x
  simp only [← max?_toArray] at h
  have := Array.max?_le_iff h (x := x)
  simpa using this

public theorem max?_eq_some_iff [Max α] [LE α] {xs : Vector α n} [Std.IsLinearOrder α]
    [Std.LawfulOrderMax α] : xs.max? = some a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → b ≤ a := by
  simp [Vector.max?, Array.max?_eq_some_iff]

public theorem max?_replicate [Max α] [Std.IdempotentOp (max : α → α → α)] {n : Nat} {a : α} :
    (replicate n a).max? = if n = 0 then none else some a := by
  simp [Vector.max?, replicate, Array.max?_replicate]

@[simp, grind =]
public theorem max?_replicate_of_pos [Max α] [Std.MaxEqOr α] {n : Nat} {a : α} (h : 0 < n) :
    (replicate n a).max? = some a := by
  simp [max?_replicate, Nat.ne_of_gt h]

public theorem foldl_max [Max α] [Std.IdempotentOp (max : α → α → α)] [Std.Associative (max : α → α → α)]
    {xs : Vector α n} {a : α} : xs.foldl (init := a) max = max a (xs.max?.getD a) := by
  simp [Vector.foldl, Vector.max?, Array.foldl_max]

/-! ### Lemmas about `min` -/

@[simp, grind =]
theorem min_singleton [Min α] {x : α} :
    #v[x].min (Nat.one_ne_zero) = x := by
  (rfl)

public theorem min?_eq_some_min [Min α] : {xs : Vector α n} → (h : n ≠ 0) →
    xs.min? = some (xs.min h)
  | ⟨xs⟩, h => by simp [Vector.min, Vector.min?, Array.min?_eq_some_min]

public theorem min_eq_get_min? [Min α] : (xs : Vector α n) → (h : n ≠ 0) →
    xs.min h = xs.min?.get (xs.isSome_min?_of_ne_zero h)
  | ⟨xs⟩, h => by simp [Vector.min, Vector.min?, Array.min_eq_get_min?]

@[simp, grind =]
public theorem get_min? [Min α] {xs : Vector α n} {h : xs.min?.isSome} :
    xs.min?.get h = xs.min (isSome_min?_iff.mp h) := by
  simp [min?_eq_some_min (isSome_min?_iff.mp h)]

@[grind .]
public theorem min_mem [Min α] [Std.MinEqOr α] {xs : Vector α n} (h : n ≠ 0) : xs.min h ∈ xs :=
  xs.min?_mem (min?_eq_some_min h)

@[grind .]
public theorem min_le_of_mem [Min α] [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderMin α]
    {xs : Vector α n} {a : α} (ha : a ∈ xs) :
    xs.min (Nat.ne_zero_iff_zero_lt.mpr (Nat.pos_of_mem_toArray ha.val)) ≤ a := by
  rw [← min_toArray]
  apply Array.min_le_of_mem
  exact ha.val

public protected theorem le_min_iff [Min α] [LE α] [Std.LawfulOrderInf α]
    {xs : Vector α n} (h : n ≠ 0) : ∀ {x}, x ≤ xs.min h ↔ ∀ b, b ∈ xs → x ≤ b :=
  le_min?_iff (min?_eq_some_min h)

public theorem min_eq_iff [Min α] [LE α] {xs : Vector α n} [Std.IsLinearOrder α] [Std.LawfulOrderMin α]
    (h : n ≠ 0) : xs.min h = a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → a ≤ b := by
  simpa [min?_eq_some_min h] using (min?_eq_some_iff (xs := xs))

@[simp, grind =]
public theorem min_replicate [Min α] [Std.MinEqOr α] {n : Nat} {a : α} (h : n ≠ 0) :
    (replicate n a).min h = a := by
  have n_pos : 0 < n := Nat.pos_iff_ne_zero.mpr h
  simpa [min?_eq_some_min h] using (min?_replicate_of_pos (a := a) n_pos)

public theorem foldl_min_eq_min [Min α] [Std.IdempotentOp (min : α → α → α)]
    [Std.Associative (min : α → α → α)] {xs : Vector α n} (h : n ≠ 0) {a : α} :
    xs.foldl min a = min a (xs.min h) := by
  simpa [min?_eq_some_min h] using foldl_min (xs := xs)

/-! ### Lemmas about `max` -/

@[simp, grind =]
theorem max_singleton [Max α] {x : α} :
    #v[x].max (Nat.one_ne_zero) = x := by
  (rfl)

public theorem max?_eq_some_max [Max α] : {xs : Vector α n} → (h : n ≠ 0) →
    xs.max? = some (xs.max h)
  | ⟨xs⟩, h => by simp [Vector.max, Vector.max?, Array.max?_eq_some_max]

public theorem max_eq_get_max? [Max α] : (xs : Vector α n) → (h : n ≠ 0) →
    xs.max h = xs.max?.get (xs.isSome_max?_of_ne_zero h)
  | ⟨xs⟩, h => by simp [Vector.max, Vector.max?, Array.max_eq_get_max?]

@[simp, grind =]
public theorem get_max? [Max α] {xs : Vector α n} {h : xs.max?.isSome} :
    xs.max?.get h = xs.max (isSome_max?_iff.mp h) := by
  simp [max?_eq_some_max (isSome_max?_iff.mp h)]

@[grind .]
public theorem max_mem [Max α] [Std.MaxEqOr α] {xs : Vector α n} (h : n ≠ 0) : xs.max h ∈ xs :=
  xs.max?_mem (max?_eq_some_max h)

public protected theorem max_le_iff [Max α] [LE α] [Std.LawfulOrderSup α]
    {xs : Vector α n} (h : n ≠ 0) : ∀ {x}, xs.max h ≤ x ↔ ∀ b, b ∈ xs → b ≤ x :=
  max?_le_iff (max?_eq_some_max h)

public theorem max_eq_iff [Max α] [LE α] {xs : Vector α n} [Std.IsLinearOrder α] [Std.LawfulOrderMax α]
    (h : n ≠ 0) : xs.max h = a ↔ a ∈ xs ∧ ∀ b, b ∈ xs → b ≤ a := by
  simpa [max?_eq_some_max h] using (max?_eq_some_iff (xs := xs))

@[grind .]
public theorem le_max_of_mem [Max α] [LE α] [Std.IsLinearOrder α] [Std.LawfulOrderMax α]
    {xs : Vector α n} {a : α} (ha : a ∈ xs) :
    a ≤ xs.max (Nat.ne_zero_iff_zero_lt.mpr (Nat.pos_of_mem_toArray ha.val)) := by
  rw [← max_toArray]
  apply Array.le_max_of_mem
  exact ha.val

@[simp, grind =]
public theorem max_replicate [Max α] [Std.MaxEqOr α] {n : Nat} {a : α} (h : n ≠ 0) :
    (replicate n a).max h = a := by
  have n_pos : 0 < n := Nat.pos_iff_ne_zero.mpr h
  simpa [max?_eq_some_max h] using (max?_replicate_of_pos (a := a) n_pos)

public theorem foldl_max_eq_max [Max α] [Std.IdempotentOp (max : α → α → α)]
    [Std.Associative (max : α → α → α)] {xs : Vector α n} (h : n ≠ 0) {a : α} :
    xs.foldl max a = max a (xs.max h) := by
  simpa [max?_eq_some_max h] using foldl_max (xs := xs)

end Vector
