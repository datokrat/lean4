import Std.Data.Iterators

/-! Good version: custom `IteratorLoop` instance WITHOUT `instance_reducible` -/

open Std Std.Iterators

-- Copy of defaultImplementation WITHOUT instance_reducible
@[always_inline, inline]
def myDefaultImpl {α : Type w} {m : Type w → Type w'} {n : Type x → Type x'}
    [Monad n] [Iterator α m β] :
    IteratorLoop α m n where
  forIn lift γ Pl it init := IterM.DefaultConsumers.forIn' lift γ Pl it init _ (fun _ => id)

@[always_inline, inline]
def IteratorLoop.myFiniteForIn' {m : Type w → Type w'} {n : Type x → Type x'}
    {α : Type w} {β : Type w} [Iterator α m β] [IteratorLoop α m n] [Monad n]
    (lift : ∀ γ δ, (γ → n δ) → m γ → n δ) :
    ForIn' n (IterM (α := α) m β) β ⟨fun it out => it.IsPlausibleIndirectOutput out⟩ where
  forIn' {γ} it init f :=
    IteratorLoop.forIn (α := α) (m := m) lift γ (fun _ _ _ => True) it init (return ⟨← f · · ·, trivial⟩)

@[always_inline, inline]
def Iter.myInstForIn' {α : Type w} {β : Type w} {n : Type x → Type x'} [Monad n]
    [Iterator α Id β] [IteratorLoop α Id n] :
    ForIn' n (Iter (α := α) β) β ⟨fun it out => it.IsPlausibleIndirectOutput out⟩ where
  forIn' it init f :=
    IteratorLoop.myFiniteForIn' (fun _ _ f c => f c.run) |>.forIn' it.toIterM init
        fun out h acc =>
          f out (Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM.mpr h) acc

instance myIterForIn {α : Type w} {β : Type w} {n : Type x → Type x'} [Monad n]
    [Iterator α Id β] [IteratorLoop α Id n] :
    ForIn n (Iter (α := α) β) β :=
  haveI := Iter.myInstForIn' (α := α) (β := β) (n := n)
  instForInOfForIn'

@[always_inline, inline]
def Iter.myFold {α : Type w} {β : Type w} {γ : Type w} [Iterator α Id β]
    [IteratorLoop α Id Id] (f : γ → β → γ)
    (init : γ) (it : Iter (α := α) β) : γ :=
  (myIterForIn (n := Id)).forIn it init (fun x acc => ForInStep.yield (f acc x))

@[always_inline, inline]
def Iter.myCount {α : Type} {β : Type} [Iterator α Id β] [IteratorLoop α Id Id]
    (it : Iter (α := α) β) : Nat :=
  Iter.myFold (fun acc _ => acc + 1) 0 it

instance (priority := high) myFilterIteratorLoop
    {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    {o : Type x → Type x'} [Monad n] [Monad o] [Iterator α m β]
    {lift : ⦃α : Type w⦄ → m α → n α}
    {f : β → PostconditionT n (Option γ)} :
    IteratorLoop (Iterators.Types.FilterMap α m n lift f) n o :=
  myDefaultImpl

set_option trace.Compiler.result true in
def myNumDivisors (n : Nat) :=
  Iter.myCount ((1...=n).iter |>.filter (n % · = 0))
