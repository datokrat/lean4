import Std.Data.Iterators

/-!
# `@[instance_reducible]` blocks `@[always_inline]` in base phase

The compiler's LCNF inlining pass (`Lean/Compiler/LCNF/Simp/InlineCandidate.lean`)
refuses to inline `instance_reducible` declarations during the base phase, even
when also marked `@[always_inline]`. The `instance_reducible` check at line 68
returns `false` BEFORE the `alwaysInlineAttr` check at line 85.

## How to read this test

1. The first part shows a simple example where `@[instance_reducible]` defers
   inlining of `@[always_inline]` from the base phase to a later phase. For
   simple scalar code this doesn't matter; both versions produce the same final IR.

2. The second part shows the real impact: when the deferred-inlining function is
   polymorphic and involves closure construction (as in the iterator `ForIn'`
   infrastructure), the base phase generates less-specialized lambdas. A later
   phase can inline the function body, but the lambda structure is already fixed,
   causing suboptimal closure construction in hot loops (~29% slowdown).
-/

/-! ## Part 1: Simple example showing deferred inlining -/

@[always_inline, inline]
def good (x : Nat) : Nat := x + 1

@[always_inline, inline, instance_reducible]
def bad (x : Nat) : Nat := x + 1

-- `good` is inlined immediately in base phase (first simp pass)
-- `bad` is NOT inlined in base phase; only inlined in a later phase
-- Both produce the same final IR, but the inlining timing differs.
set_option trace.Compiler.simp.inline true in
set_option trace.Compiler.simp.step true in
def usesGood (x : Nat) : Nat := good (good x)

set_option trace.Compiler.simp.inline true in
set_option trace.Compiler.simp.step true in
def usesBad (x : Nat) : Nat := bad (bad x)

/-! ## Part 2: Impact on iterator `ForIn'` infrastructure

When `instance_reducible` is added to the polymorphic `ForIn'` bridge functions,
the base phase can't inline them, producing different lambda structures.

Compare the `_lam_3` in `goodForIn` (specialized, from inlining `goodInstForIn'`)
vs the `_lam_2` in `badForIn` (generic, reused from `goodForIn'` because
`badInstForIn'` wasn't inlined in the base phase).
-/

open Std Std.Iterators

-- Version WITHOUT instance_reducible
@[always_inline, inline]
def IteratorLoop.goodForIn' {m : Type w → Type w'} {n : Type x → Type x'}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoop α m n] [Monad n]
    (lift : ∀ γ δ, (γ → n δ) → m γ → n δ) :
    ForIn' n (IterM (α := α) m β) β ⟨fun it out => it.IsPlausibleIndirectOutput out⟩ where
  forIn' {γ} it init f :=
    IteratorLoop.forIn (α := α) (m := m) lift γ (fun _ _ _ => True) it init (return ⟨← f · · ·, trivial⟩)

@[always_inline, inline]
def IterM.goodInstForIn' {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoop α m n] [Monad n]
    [MonadLiftT m n] :
    ForIn' n (IterM (α := α) m β) β ⟨fun it out => it.IsPlausibleIndirectOutput out⟩ :=
  IteratorLoop.goodForIn' (fun _ _ f x => monadLift x >>= f)

-- Version WITH instance_reducible
@[always_inline, inline, instance_reducible]
def IteratorLoop.badForIn' {m : Type w → Type w'} {n : Type x → Type x'}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoop α m n] [Monad n]
    (lift : ∀ γ δ, (γ → n δ) → m γ → n δ) :
    ForIn' n (IterM (α := α) m β) β ⟨fun it out => it.IsPlausibleIndirectOutput out⟩ where
  forIn' {γ} it init f :=
    IteratorLoop.forIn (α := α) (m := m) lift γ (fun _ _ _ => True) it init (return ⟨← f · · ·, trivial⟩)

@[always_inline, inline, instance_reducible]
def IterM.badInstForIn' {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoop α m n] [Monad n]
    [MonadLiftT m n] :
    ForIn' n (IterM (α := α) m β) β ⟨fun it out => it.IsPlausibleIndirectOutput out⟩ :=
  IteratorLoop.badForIn' (fun _ _ f x => monadLift x >>= f)

-- Trace the ForIn instances to compare lambda structure.
-- Key difference: goodForIn uses `IterM.goodInstForIn'._redArg._lam_3` (specialized)
-- while badForIn uses `IteratorLoop.goodForIn'._redArg._lam_2` (generic, not specialized).
set_option trace.Compiler.result true in
instance goodForIn {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoop α m n]
    [MonadLiftT m n] [Monad n] :
    ForIn n (IterM (α := α) m β) β :=
  haveI : ForIn' n (IterM (α := α) m β) β _ := IterM.goodInstForIn'
  instForInOfForIn'

set_option trace.Compiler.result true in
instance badForIn {m : Type w → Type w'} {n : Type w → Type w''}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoop α m n]
    [MonadLiftT m n] [Monad n] :
    ForIn n (IterM (α := α) m β) β :=
  haveI : ForIn' n (IterM (α := α) m β) β _ := IterM.badInstForIn'
  instForInOfForIn'
