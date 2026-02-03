/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.Order.WellFounded

/-!
# Definitions of conditionally complete lattices

A conditionally complete lattice is a lattice in which every non-empty bounded subset `s`
has a least upper bound and a greatest lower bound, denoted below by `sSup s` and `sInf s`.
Typical examples are `ℝ`, `ℕ`, and `ℤ` with their usual orders.

The theory is very comparable to the theory of complete lattices, except that suitable
boundedness and nonemptiness assumptions have to be added to most statements.
We express these using the `BddAbove` and `BddBelow` predicates, which we use to prove
most useful properties of `sSup` and `sInf` in conditionally complete lattices.

To differentiate the statements between complete lattices and conditionally complete
lattices, we prefix `sInf` and `sSup` in the statements by `c`, giving `csInf` and `csSup`.
For instance, `sInf_le` is a statement in complete lattices ensuring `sInf s ≤ x`,
while `csInf_le` is the same statement in conditionally complete lattices
with an additional assumption that `s` is bounded below.
-/

@[expose] public section

open Set

variable {α β γ : Type*} {ι : Sort*}

/-- A conditionally complete lattice is a lattice in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete lattices, we prefix `sInf` and `sSup` by a `c` everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness. -/
class ConditionallyCompleteLattice (α : Type*) extends Lattice α where
  /-- Every nonempty subset which is bounded above has a least upper bound. -/
  exists_isLUB_of_nonempty_of_bddAbove : ∀ s : Set α, s.Nonempty → BddAbove s → ∃ a, IsLUB s a
  /-- Every nonempty subset which is bounded below has a greatest lower bound. -/
  exists_isGLB_of_nonempty_of_bddBelow : ∀ s : Set α, s.Nonempty → BddBelow s → ∃ a, IsGLB s a

/-- A conditionally complete linear order is a linear order in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix `sInf` and `sSup` by a `c` everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness. -/
class ConditionallyCompleteLinearOrder (α : Type*)
    extends ConditionallyCompleteLattice α, Ord α where
  /-- A `ConditionallyCompleteLinearOrder` is total. -/
  le_total (a b : α) : a ≤ b ∨ b ≤ a
  /-- In a `ConditionallyCompleteLinearOrder`, we assume the order relations are all decidable. -/
  toDecidableLE : DecidableLE α
  /-- In a `ConditionallyCompleteLinearOrder`, we assume the order relations are all decidable. -/
  toDecidableEq : DecidableEq α := @decidableEqOfDecidableLE _ _ toDecidableLE
  /-- In a `ConditionallyCompleteLinearOrder`, we assume the order relations are all decidable. -/
  toDecidableLT : DecidableLT α := @decidableLTOfDecidableLE _ _ toDecidableLE
  compare a b := compareOfLessAndEq a b
  /-- Comparison via `compare` is equal to the canonical comparison given decidable `<` and `=`. -/
  compare_eq_compareOfLessAndEq : ∀ a b, compare a b = compareOfLessAndEq a b := by
    compareOfLessAndEq_rfl

/-- A conditionally complete linear order with `Bot` is a linear order with least element, in which
every nonempty subset which is bounded above has a supremum, and every nonempty subset (necessarily
bounded below) has an infimum.  A typical example is the natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix `sInf` and `sSup` by a `c` everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness. -/
class ConditionallyCompleteLinearOrderBot (α : Type*) extends ConditionallyCompleteLinearOrder α,
    OrderBot α where

-- see Note [lower instance priority]
attribute [instance 100] ConditionallyCompleteLinearOrderBot.toOrderBot

/-- Create a `ConditionallyCompleteLattice` from a `PartialOrder` and `sup` function
that returns the least upper bound of a nonempty set which is bounded above. Usually this
constructor provides poor definitional equalities.  If other fields are known explicitly, they
should be provided; for example, if `inf` is known explicitly, construct the
`ConditionallyCompleteLattice` instance as
```
instance : ConditionallyCompleteLattice my_T :=
  { inf := better_inf,
    le_inf := ...,
    inf_le_right := ...,
    inf_le_left := ...
    -- don't care to fix sup
    ..conditionallyCompleteLatticeOfsSup my_T _ }
```
-/
def conditionallyCompleteLatticeOfsSup (α : Type*) [H1 : PartialOrder α] (sSup' : Set α → α)
    (bddAbove_pair : ∀ a b : α, BddAbove ({a, b} : Set α))
    (bddBelow_pair : ∀ a b : α, BddBelow ({a, b} : Set α))
    (isLUB_sSup' : ∀ s : Set α, s.Nonempty → BddAbove s → IsLUB s (sSup' s)) :
    ConditionallyCompleteLattice α :=
  { H1 with
    sup := fun a b => sSup' {a, b}
    le_sup_left := fun a b =>
      (isLUB_sSup' {a, b} (insert_nonempty _ _) (bddAbove_pair a b)).1 (mem_insert _ _)
    le_sup_right := fun a b =>
      (isLUB_sSup' {a, b} (insert_nonempty _ _) (bddAbove_pair a b)).1
        (mem_insert_of_mem _ (mem_singleton _))
    sup_le := fun a b _ hac hbc =>
      (isLUB_sSup' {a, b} (insert_nonempty _ _) (bddAbove_pair a b)).2
        (forall_insert_of_forall (forall_eq.mpr hbc) hac)
    inf := fun a b => sSup' (lowerBounds {a, b})
    inf_le_left := fun a b =>
      (isLUB_sSup' (lowerBounds {a, b}) (bddBelow_pair a b)
          (insert_nonempty _ _).bddAbove_lowerBounds).2
        fun _ hc => hc <| mem_insert _ _
    inf_le_right := fun a b =>
      (isLUB_sSup' (lowerBounds {a, b}) (bddBelow_pair a b)
          (insert_nonempty _ _).bddAbove_lowerBounds).2
        fun _ hc => hc <| mem_insert_of_mem _ (mem_singleton _)
    le_inf := fun c a b hca hcb =>
      (isLUB_sSup' (lowerBounds {a, b}) ⟨c, forall_insert_of_forall (forall_eq.mpr hcb) hca⟩
          (insert_nonempty _ _).bddAbove_lowerBounds).1
        (forall_insert_of_forall (forall_eq.mpr hcb) hca)
    exists_isLUB_of_nonempty_of_bddAbove _ hn hb := ⟨_, isLUB_sSup' _ hn hb⟩
    exists_isGLB_of_nonempty_of_bddBelow s hn hb := ⟨sSup' (lowerBounds s),
      @fun _ ha ↦ (isLUB_sSup' (lowerBounds s) hb hn.bddAbove_lowerBounds).2 fun _ hb ↦ hb ha,
      @fun _ ha ↦ (isLUB_sSup' (lowerBounds s) ⟨_, ha⟩ hn.bddAbove_lowerBounds).1 ha⟩ }

/-- Create a `ConditionallyCompleteLattice` from a `PartialOrder` and `inf` function
that returns the greatest lower bound of a nonempty set which is bounded below. Usually this
constructor provides poor definitional equalities.  If other fields are known explicitly, they
should be provided; for example, if `inf` is known explicitly, construct the
`ConditionallyCompleteLattice` instance as
```
instance : ConditionallyCompleteLattice my_T :=
  { inf := better_inf,
    le_inf := ...,
    inf_le_right := ...,
    inf_le_left := ...
    -- don't care to fix sup
    ..conditionallyCompleteLatticeOfsInf my_T _ }
```
-/
def conditionallyCompleteLatticeOfsInf (α : Type*) [H1 : PartialOrder α] (sInf' : Set α → α)
    (bddAbove_pair : ∀ a b : α, BddAbove ({a, b} : Set α))
    (bddBelow_pair : ∀ a b : α, BddBelow ({a, b} : Set α))
    (isGLB_sInf' : ∀ s : Set α, s.Nonempty → BddBelow s → IsGLB s (sInf' s)) :
    ConditionallyCompleteLattice α :=
  { H1 with
    inf := fun a b => sInf' {a, b}
    inf_le_left := fun a b =>
      (isGLB_sInf' {a, b} (insert_nonempty _ _) (bddBelow_pair a b)).1 (mem_insert _ _)
    inf_le_right := fun a b =>
      (isGLB_sInf' {a, b} (insert_nonempty _ _) (bddBelow_pair a b)).1
        (mem_insert_of_mem _ (mem_singleton _))
    le_inf := fun _ a b hca hcb =>
      (isGLB_sInf' {a, b} (insert_nonempty _ _) (bddBelow_pair a b)).2
        (forall_insert_of_forall (forall_eq.mpr hcb) hca)
    sup := fun a b => sInf' (upperBounds {a, b})
    le_sup_left := fun a b =>
      (isGLB_sInf' (upperBounds {a, b}) (bddAbove_pair a b)
          (insert_nonempty _ _).bddBelow_upperBounds).2
        fun _ hc => hc <| mem_insert _ _
    le_sup_right := fun a b =>
      (isGLB_sInf' (upperBounds {a, b}) (bddAbove_pair a b)
          (insert_nonempty _ _).bddBelow_upperBounds).2
        fun _ hc => hc <| mem_insert_of_mem _ (mem_singleton _)
    sup_le := fun a b c hac hbc =>
      (isGLB_sInf' (upperBounds {a, b}) ⟨c, forall_insert_of_forall (forall_eq.mpr hbc) hac⟩
          (insert_nonempty _ _).bddBelow_upperBounds).1
        (forall_insert_of_forall (forall_eq.mpr hbc) hac)
    exists_isGLB_of_nonempty_of_bddBelow _ hn hb := ⟨_, isGLB_sInf' _ hn hb⟩
    exists_isLUB_of_nonempty_of_bddAbove s hn hb := ⟨sInf' (upperBounds s),
      @fun _ ha ↦ (isGLB_sInf' (upperBounds s) hb hn.bddBelow_upperBounds).2 fun _ hb ↦ hb ha,
      @fun _ ha ↦ (isGLB_sInf' (upperBounds s) ⟨_, ha⟩ hn.bddBelow_upperBounds).1 ha⟩ }

/-- A version of `conditionallyCompleteLatticeOfsSup` when we already know that `α` is a lattice.

This should only be used when it is both hard and unnecessary to provide `inf` explicitly. -/
def conditionallyCompleteLatticeOfLatticeOfsSup (α : Type*) [H1 : Lattice α] (sSup' : Set α → α)
    (isLUB_sSup' : ∀ s : Set α, s.Nonempty → BddAbove s → IsLUB s (sSup' s)) :
    ConditionallyCompleteLattice α :=
  { H1,
    conditionallyCompleteLatticeOfsSup α _
      (fun a b => ⟨a ⊔ b, forall_insert_of_forall (forall_eq.mpr le_sup_right) le_sup_left⟩)
      (fun a b => ⟨a ⊓ b, forall_insert_of_forall (forall_eq.mpr inf_le_right) inf_le_left⟩)
      isLUB_sSup' with }

/-- A version of `conditionallyCompleteLatticeOfsInf` when we already know that `α` is a lattice.

This should only be used when it is both hard and unnecessary to provide `sup` explicitly. -/
def conditionallyCompleteLatticeOfLatticeOfsInf (α : Type*) [H1 : Lattice α] (sInf' : Set α → α)
    (isGLB_sInf' : ∀ s : Set α, s.Nonempty → BddBelow s → IsGLB s (sInf' s)) :
    ConditionallyCompleteLattice α :=
  { H1,
    conditionallyCompleteLatticeOfsInf α _
      (fun a b => ⟨a ⊔ b, forall_insert_of_forall (forall_eq.mpr le_sup_right) le_sup_left⟩)
      (fun a b => ⟨a ⊓ b, forall_insert_of_forall (forall_eq.mpr inf_le_right) inf_le_left⟩)
      isGLB_sInf' with }

open scoped Classical in
/-- A well-founded linear order is conditionally complete, with a bottom element. -/
noncomputable abbrev WellFoundedLT.conditionallyCompleteLinearOrderBot (α : Type*)
    [i₁ : LinearOrder α] [i₂ : OrderBot α] [h : WellFoundedLT α] :
    ConditionallyCompleteLinearOrderBot α :=
  { i₁, i₂, LinearOrder.toLattice,
    conditionallyCompleteLatticeOfLatticeOfsInf _
      (fun s => if hs : s.Nonempty then h.wf.min s hs else ⊥)
      (fun s hn hb ↦ by
        simpa [dif_pos hn] using IsLeast.isGLB ⟨h.wf.min_mem s hn, fun x hx ↦ h.wf.min_le hx hn⟩)
    with }

lemma exists_isLUB_of_nonempty_of_bddAbove [ConditionallyCompleteLattice α] {s : Set α} :
    s.Nonempty → BddAbove s → ∃ a, IsLUB s a :=
  ConditionallyCompleteLattice.exists_isLUB_of_nonempty_of_bddAbove _

lemma exists_isGLB_of_nonempty_of_bddBelow [ConditionallyCompleteLattice α] {s : Set α} :
    s.Nonempty → BddBelow s → ∃ a, IsGLB s a :=
  ConditionallyCompleteLattice.exists_isGLB_of_nonempty_of_bddBelow _
