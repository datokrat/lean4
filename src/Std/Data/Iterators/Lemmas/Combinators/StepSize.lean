/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers.Access
public import Init.Data.Iterators.Consumers.Collect
public import Init.Data.Iterators.Combinators.Take
public import Std.Data.Iterators.Combinators.StepSize
import Init.Data.Iterators.Lemmas.Consumers.Access

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

theorem _root_.Std.IterM.step_stepSize [Iterator α Id β] [Productive α Id] [LawfulDeterministicIterator α Id]
    [IteratorAccess α Id] {it : IterM (α := α) Id β} {n : Nat} :
    it.nextAtIdx? n = it.nextAtIdxSlow? n := by
  ext
  apply Subsingleton.allEq

theorem step_stepSize [Iterator α Id β] [Productive α Id] [LawfulDeterministicIterator α Id]
    [IteratorAccess α Id] {it : Iter (α := α) β} {n : Nat} :
    it.nextAtIdx? n = it.nextAtIdxSlow? n := by
  simp [Iter.nextAtIdx?, Iter.nextAtIdxSlow?, IterM.step_stepSize]

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
