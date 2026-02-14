/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers.Access
public import Init.Data.Iterators.Consumers.Collect
public import Init.Data.Iterators.Consumers.Loop
public import Init.Data.Iterators.Combinators.Take
public import Std.Data.Iterators.Combinators.StepSize
import Init.Data.Iterators.Lemmas.Consumers.Access
import Init.Data.Iterators.Lemmas.Consumers.Monadic.Access
import Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop
import Init.Data.Iterators.Lemmas.Monadic.Basic
import all Init.Data.Iterators.Consumers.Monadic.Access
import all Std.Data.Iterators.Combinators.StepSize

public section
open Std Std.Iterators Std.Iterators.Types

namespace Std.Iter

-- example [Iterator α Id β] [IteratorAccess α Id] [LawfulDeterministicIterator α Id] :
--     Productive α Id where
--   wf := by
--     constructor
--     intro it
--     have :=

-- instance [Iterator α m β] [LawfulDeterministicIterator α m] [IteratorAccess α m] [Monad m] :
--     LawfulDeterministicIterator (StepSizeIterator α m β) m where
--   isPlausibleStep_eq_eq it := by
--     simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, funext_iff]
--     obtain ⟨⟨

-- theorem step_stepSize

instance [Iterator α Id β] [LawfulDeterministicIterator α Id] {it : IterM (α := α) Id β} :
    Subsingleton it.Step where
  allEq s s' := by
    obtain ⟨s'', hs''⟩ := LawfulDeterministicIterator.isPlausibleStep_eq_eq it
    obtain ⟨s, hs⟩ := s
    obtain ⟨s', hs'⟩ := s'
    simp only [hs''] at hs hs'
    have := hs.trans hs'.symm
    rwa [Subtype.mk.injEq]

instance [Iterator α Id β] [LawfulDeterministicIterator α Id] {it : Iter (α := α) β} :
    Subsingleton it.Step where
  allEq s s' := by
    obtain ⟨s'', hs''⟩ := LawfulDeterministicIterator.isPlausibleStep_eq_eq it.toIterM
    obtain ⟨s, hs⟩ := s
    obtain ⟨s', hs'⟩ := s'
    simp only [Iter.IsPlausibleStep, hs''] at hs hs'
    have := hs.trans hs'.symm
    rw [IterStep.mapIterator_inj (fun _ _ => toIterM_inj.mp) ] at this
    rwa [Subtype.mk.injEq]

theorem eq_step_of_isPlausibleStep [Iterator α Id β] [LawfulDeterministicIterator α Id]
    {it : Iter (α := α) β} {step} (h : it.IsPlausibleStep step) :
    step = it.step.val := by
  have : ⟨step, h⟩ = it.step := Subsingleton.allEq _ _
  simp [← this]

theorem _root_.Std.IterM.eq_step_of_isPlausibleStep [Iterator α Id β] [LawfulDeterministicIterator α Id]
    {it : IterM (α := α) Id β} {step} (h : it.IsPlausibleStep step) :
    step = it.step.run.inflate.val := by
  have : ⟨step, h⟩ = it.step.run.inflate := Subsingleton.allEq _ _
  simp [← this]

theorem _root_.Std.IterM.eq_of_isPlausibleNthOutputStep_of_isPlausibleNthOutputStep [Iterator α Id β]
    [LawfulDeterministicIterator α Id]
    {it : IterM (α := α) Id β} {s s'}
    (hs : it.IsPlausibleNthOutputStep n s)
    (hs' : it.IsPlausibleNthOutputStep n s') :
    s = s' := by
  induction hs
  case zero_yield h =>
    match hs' with
    | .zero_yield h' ..
    | .skip h' ..
    | .done h' =>
      replace h := IterM.eq_step_of_isPlausibleStep h
      replace h' := IterM.eq_step_of_isPlausibleStep h'
      rw [← h] at h'
      cases h'
      all_goals rfl
  case done h =>
    match hs' with
    | .zero_yield h' ..
    | .yield h' ..
    | .skip h' ..
    | .done h' =>
      replace h := IterM.eq_step_of_isPlausibleStep h
      replace h' := IterM.eq_step_of_isPlausibleStep h'
      rw [← h] at h'
      all_goals cases h'
      all_goals rfl
  case yield h _ ih =>
    match hs' with
    | .yield h' ..
    | .skip h' ..
    | .done h' =>
      replace h := IterM.eq_step_of_isPlausibleStep h
      replace h' := IterM.eq_step_of_isPlausibleStep h'
      rw [← h] at h'
      cases h'
      all_goals
        apply ih ‹_›
  case skip h _ ih =>
    match hs' with
    | .zero_yield h' ..
    | .yield h' ..
    | .skip h' ..
    | .done h' =>
      replace h := IterM.eq_step_of_isPlausibleStep h
      replace h' := IterM.eq_step_of_isPlausibleStep h'
      rw [← h] at h'
      cases h'
      all_goals
        apply ih ‹_›

instance [Iterator α Id β] [LawfulDeterministicIterator α Id] {it : IterM (α := α) Id β} :
    Subsingleton (PlausibleIterStep (it.IsPlausibleNthOutputStep n)) where
  allEq s s' := by
    obtain ⟨s, hs⟩ := s
    obtain ⟨s', hs'⟩ := s'
    have := IterM.eq_of_isPlausibleNthOutputStep_of_isPlausibleNthOutputStep hs hs'
    rwa [Subtype.mk.injEq]

theorem _root_.Std.IterM.nextAtIdx?_eq_nextAtIdxSlow? [Iterator α Id β] [Productive α Id] [LawfulDeterministicIterator α Id]
    [IteratorAccess α Id] {it : IterM (α := α) Id β} {n : Nat} :
    it.nextAtIdx? n = it.nextAtIdxSlow? n := by
  ext
  apply Subsingleton.allEq

theorem nextAtIdx?_eq_nextAtIdxSlow? [Iterator α Id β] [Productive α Id] [LawfulDeterministicIterator α Id]
    [IteratorAccess α Id] {it : Iter (α := α) β} {n : Nat} :
    it.nextAtIdx? n = it.nextAtIdxSlow? n := by
  simp [Iter.nextAtIdx?, Iter.nextAtIdxSlow?, IterM.nextAtIdx?_eq_nextAtIdxSlow?]

theorem _root_.Std.IterM.nextAtIdxSlow?_stepSize_aux [Iterator α Id β] [Productive α Id] [LawfulDeterministicIterator α Id]
    [IteratorAccess α Id] {it : IterM (α := α) Id β} {n : Nat} :
    (IterM.Intermediate.stepSize it i n).nextAtIdxSlow? 0 = (do
      match (← it.nextAtIdxSlow? i) with
      | .yield it' out h =>
        return .yield (IterM.Intermediate.stepSize it' (n - 1) n) out (by
          refine .zero_yield ?_
          simpa [IterM.IsPlausibleStep, Iterator.IsPlausibleStep,
            IterM.Intermediate.stepSize, IterM.Intermediate.stepSize])
      | .skip it' h => return IterM.not_isPlausibleNthOutputStep_skip.elim h
      | .done h =>
        return .done (by
          refine .done ?_
          simpa [IterM.IsPlausibleStep, Iterator.IsPlausibleStep,
            Intermediate.stepSize, IterM.Intermediate.stepSize])) := by
  induction it, i using IterM.atIdxSlow?.induct_unfolding
  simp [IterM.Intermediate.stepSize]
  rw [IterM.nextAtIdxSlow?_eq_match]
  simp [IterM.step_eq, IterM.nextAtIdx?_eq_nextAtIdxSlow?]
  apply bind_congr; intro step
  cases step using PlausibleIterStep.casesOn
  · simp
  · exact IterM.not_isPlausibleNthOutputStep_skip.elim ‹_›
  · simp

theorem _root_.Std.IterM.length_nextAtIdxSlow? [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} :
    (do match ← it.nextAtIdxSlow? n with
      | .yield it' out _ => it'.length
      | .skip it' h => IterM.not_isPlausibleNthOutputStep_skip.elim h
      | .done h => return .up 0) = (fun len => .up (len.down - n - 1)) <$> it.length := by
  induction it using IterM.inductSteps generalizing n with | step it ihy ihs
  rw [it.nextAtIdxSlow?_eq_match, it.length_eq_match_step]
  simp only [map_eq_pure_bind, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp
    split
    · simp
    · rename_i it' out h n n'
      simp
      refine Eq.trans ?_ ((ihy h (n := n')).trans ?_)
      · apply bind_congr; intro step
        cases step using PlausibleIterStep.casesOn
        · simp
        · rfl
        · simp
      · simp [Nat.add_sub_add_right]
  · rename_i it' h n _ h
    simp
    refine Eq.trans ?_ ((ihs h (n := n)).trans ?_)
    · apply bind_congr; intro step
      cases step using PlausibleIterStep.casesOn
      · simp
      · rfl
      · simp
    · simp
  · simp

theorem length_nextAtIdxSlow? [Iterator α Id β] [Finite α Id] [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    {it : Iter (α := α) β} :
    (match it.nextAtIdxSlow? n with
      | .yield it' out _ => it'.length
      | .skip it' h => IterM.not_isPlausibleNthOutputStep_skip.elim h
      | .done h => 0) = it.length - n - 1 := by
  have := IterM.length_nextAtIdxSlow? (it := it.toIterM) (n := n)
  replace this := congrArg Id.run this
  replace this := congrArg ULift.down this
  simp at this
  simp [Iter.length, ← this, Iter.nextAtIdxSlow?]
  split at this
  · simp [*]
  · exact IterM.not_isPlausibleNthOutputStep_skip.elim ‹_›
  · simp [*]

theorem _root_.Std.IterM.length_stepSize [Iterator α Id β] [Finite α Id] [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    [IteratorAccess α Id] {it : IterM (α := α) Id β} :
    (IterM.Intermediate.stepSize it i n).length.run.down = (it.length.run.down + (n - 1) - i) / (n - 1 + 1) := by
  induction n generalizing it i
  · rw [IterM.length_eq_match_step, IterM.length_eq_match_step, IterM.step_eq]
    simp [IterM.Intermediate.stepSize]
    cases (it.nextAtIdx? i).run using PlausibleIterStep.casesOn
    · simp
      rw [IterM.length_eq_match_step]
      simp

theorem _root_.Std.IterM.step_stepSize [Iterator α Id β] [Finite α Id] [LawfulDeterministicIterator α Id]
    [IteratorAccess α Id] {it : IterM (α := α) Id β} :
    (IterM.Intermediate.stepSize it i n).step.run.inflate.val =
      match it.step.run.inflate.val with
      | .yield it' out =>
        match i with
        | 0 => .yield (IterM.Intermediate.stepSize it' (n - 1) n) out
        | i + 1 => .skip (IterM.Intermediate.stepSize it' i n)
      | .skip it' => .skip (IterM.Intermediate.stepSize it' i n)
      | .done => .done := by
  rw [IterM.step_eq]
  simp [IterM.Intermediate.stepSize, IterM.nextAtIdx?_eq_nextAtIdxSlow?]
  rw [IterM.nextAtIdxSlow?_eq_match]
  simp
  cases it.step.run.inflate using PlausibleIterStep.casesOn
  · simp
    split
    · simp
    · simp


theorem _root_.Std.IterM.length_stepSize [Iterator α Id β] [Finite α Id] [LawfulDeterministicIterator α Id]
    [IteratorAccess α Id] [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id] {it : IterM (α := α) Id β} {i n : Nat} :
    (IterM.Intermediate.stepSize it i n).length.run.down = (it.length.run.down + (n - 1) - i) / (n - 1 + 1) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [IterM.length_eq_match_step, IterM.length_eq_match_step, step_stepSize]

theorem atIdxSlow?_stepSize_aux [Iterator α Id β] [Productive α Id] [LawfulDeterministicIterator α Id]
    [IteratorAccess α Id] {it : Iter (α := α) β} {n : Nat} :
    (Intermediate.stepSize it i n).nextAtIdxSlow? 0 =
      match it.nextAtIdxSlow? i with
      | .yield it' out h =>
        .yield (Intermediate.stepSize it' (n - 1) n) out (by
          refine .zero_yield ?_
          simpa [IterM.IsPlausibleStep, Iterator.IsPlausibleStep,
            Intermediate.stepSize, IterM.Intermediate.stepSize])
      | .skip it' h => IterM.not_isPlausibleNthOutputStep_skip.elim h
      | .done h =>
        .done (by
          refine .done ?_
          simpa [IterM.IsPlausibleStep, Iterator.IsPlausibleStep,
            Intermediate.stepSize, IterM.Intermediate.stepSize]) := by
  simp only [Iter.nextAtIdxSlow?]
  simp only [Intermediate.stepSize, toIterM_toIter, IterM.nextAtIdxSlow?_stepSize_aux]
  simp
  apply Subtype.ext
  simp
  let step := (it.toIterM.nextAtIdxSlow? i).run
  cases hs : step using PlausibleIterStep.casesOn
  · simp [show (it.toIterM.nextAtIdxSlow? i).run = step from rfl]
    simp [hs]
  · exact IterM.not_isPlausibleNthOutputStep_skip.elim ‹_›
  · simp [show (it.toIterM.nextAtIdxSlow? i).run = step from rfl]
    simp [hs]

theorem atIdxSlow?_stepSize_aux [Iterator α Id β] [Productive α Id] [LawfulDeterministicIterator α Id]
    [IteratorAccess α Id] {it : Iter (α := α) β} {n : Nat} :
    (Iter.Intermediate.stepSize it i n).atIdxSlow? k = it.atIdxSlow? (i + (n - 1 + 1) * k) := by
  induction k
  · simp
    induction i, it using Iter.atIdxSlow?.induct_unfolding
    case yield_zero it it' _ h _ =>
      rw [atIdxSlow?_eq_match]
      simp [Intermediate.stepSize, IterM.Intermediate.stepSize, Iter.step_eq]
      cases (it.toIterM.nextAtIdx? 0).run using PlausibleIterStep.casesOn
      · rename_i h'
        simp [Iter.IsPlausibleStep] at h
        replace h := IterM.IsPlausibleNthOutputStep.zero_yield h
        cases IterM.eq_of_isPlausibleNthOutputStep_of_isPlausibleNthOutputStep h h'
        simp
      · rename_i h'
        simp [Iter.IsPlausibleStep] at h
        replace h := IterM.IsPlausibleNthOutputStep.zero_yield h
        cases IterM.eq_of_isPlausibleNthOutputStep_of_isPlausibleNthOutputStep h h'
      · rename_i h'
        simp [Iter.IsPlausibleStep] at h
        replace h := IterM.IsPlausibleNthOutputStep.zero_yield h
        cases IterM.eq_of_isPlausibleNthOutputStep_of_isPlausibleNthOutputStep h h'
    case yield_succ it it' _ h _ =>
      rw [atIdxSlow?_eq_match, atIdxSlow?_eq_match]

  generalize h : Iter.Intermediate.stepSize it i n = sit
  induction k, sit using Iter.atIdxSlow?.induct_unfolding
  case yield_zero =>
    simp
    simp [Intermediate.stepSize, IterM.Intermediate.stepSize] at h

theorem atIdxSlow?_stepSize [Iterator α Id β] [Productive α Id] [LawfulDeterministicIterator α Id]
    [IteratorAccess α Id] {it : Iter (α := α) β} {n : Nat} :
    (it.stepSize n).atIdxSlow? k = it.atIdxSlow? ((n - 1 + 1) * k) := by


end Std.Iter
