/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers.Access
import Init.Data.Iterators.Lemmas.Consumers.Monadic.Access

namespace Std.Iter
open Std.Iterators

public theorem nextAtIdxSlow?_eq_match [Iterator α Id β] [Productive α Id]
    {n : Nat} {it : Iter (α := α) β} :
    it.nextAtIdxSlow? n =
      (match it.step with
      | .yield it' out hp =>
        match n with
        | 0 => .yield it' out (.zero_yield hp)
        | n + 1 =>
          let s := it'.nextAtIdxSlow? n
          ⟨s.val, .yield hp s.property⟩
      | .skip it' hp =>
        let s := it'.nextAtIdxSlow? n
        ⟨s.val, .skip hp s.property⟩
      | .done hp => .done (.done hp)) := by
  simp [Iter.nextAtIdxSlow?]
  apply Subtype.ext
  simp only
  rw [IterM.nextAtIdxSlow?_eq_match]
  simp only [bind_pure_comp, Id.run_bind, step]
  split
  · cases n <;> simp [*]
  · simp [*]
  · simp [*]

public theorem atIdxSlow?_eq_match [Iterator α Id β] [Productive α Id]
    {n : Nat} {it : Iter (α := α) β} :
    it.atIdxSlow? n =
      (match it.step.val with
      | .yield it' out =>
        match n with
        | 0 => some out
        | n + 1 => it'.atIdxSlow? n
      | .skip it' => it'.atIdxSlow? n
      | .done => none) := by
  induction n, it using Iter.atIdxSlow?.induct_unfolding <;> simp_all

end Std.Iter
