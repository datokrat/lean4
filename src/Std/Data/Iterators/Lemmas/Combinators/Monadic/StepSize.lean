/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.Iterators.Combinators.Monadic.StepSize

public section
open Std Std.Iterators Std.Iterators.Types

namespace Std.IterM

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

end Std.IterM
