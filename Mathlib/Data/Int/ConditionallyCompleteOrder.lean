/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Data.Int.LeastGreatest
public import Mathlib.Order.ConditionallyCompleteLattice.Defs

/-!
## `ℤ` forms a conditionally complete linear order

The integers form a conditionally complete linear order.
-/

@[expose] public section


open Int


noncomputable section

open scoped Classical in
instance instConditionallyCompleteLinearOrder : ConditionallyCompleteLinearOrder ℤ where
  __ := instLinearOrder
  __ := LinearOrder.toLattice
  exists_isLUB_cond _ hn := fun ⟨_, hb⟩ ↦ ⟨_, (isGreatest_coe_greatestOfBdd _ hb hn).isLUB⟩
  exists_isGLB_cond _ hn := fun ⟨_, hb⟩ ↦ ⟨_, (isLeast_coe_leastOfBdd _ hb hn).isGLB⟩

namespace Int

theorem csSup_eq_greatestOfBdd {s : Set ℤ} [DecidablePred (· ∈ s)] (b : ℤ) (Hb : ∀ z ∈ s, z ≤ b)
    (Hinh : ∃ z : ℤ, z ∈ s) : sSup s = greatestOfBdd b Hb Hinh :=
  (isGreatest_coe_greatestOfBdd _ Hb Hinh).isLUB.sSup_eq

@[deprecated (since := "2025-12-24")] alias csSup_eq_greatest_of_bdd := csSup_eq_greatestOfBdd

instance : NoBotOrder ℤ := ⟨fun x ↦ ⟨x - 1, (Int.sub_one_lt_of_le le_rfl).not_ge⟩⟩
instance : NoTopOrder ℤ := ⟨fun x ↦ ⟨x + 1, (Int.lt_add_one_of_le le_rfl).not_ge⟩⟩

@[deprecated NoBotOrder.sSup_empty (since := "2026-03-29")]
theorem csSup_empty : sSup (∅ : Set ℤ) = Classical.arbitrary ℤ :=
  NoBotOrder.sSup_empty

@[deprecated sSup_of_not_bddAbove (since := "2026-03-29")]
theorem csSup_of_not_bddAbove {s : Set ℤ} (h : ¬BddAbove s) : sSup s = Classical.arbitrary ℤ :=
  sSup_of_not_bddAbove h

@[deprecated (since := "2025-12-24")] alias csSup_of_not_bdd_above := csSup_of_not_bddAbove

theorem csInf_eq_leastOfBdd {s : Set ℤ} [DecidablePred (· ∈ s)] (b : ℤ) (Hb : ∀ z ∈ s, b ≤ z)
    (Hinh : ∃ z : ℤ, z ∈ s) : sInf s = leastOfBdd b Hb Hinh :=
  (isLeast_coe_leastOfBdd _ Hb Hinh).isGLB.sInf_eq

@[deprecated (since := "2025-12-24")] alias csInf_eq_least_of_bdd := csInf_eq_leastOfBdd

@[deprecated NoTopOrder.sInf_empty (since := "2026-03-29")]
theorem csInf_empty : sInf (∅ : Set ℤ) = Classical.arbitrary ℤ :=
  NoTopOrder.sInf_empty

@[deprecated sInf_of_not_bddBelow (since := "2026-03-29")]
theorem csInf_of_not_bddBelow {s : Set ℤ} (h : ¬BddBelow s) : sInf s = Classical.arbitrary ℤ :=
  sInf_of_not_bddBelow h

@[deprecated (since := "2025-12-24")] alias csInf_of_not_bdd_below := csInf_of_not_bddBelow

theorem csSup_mem {s : Set ℤ} (h1 : s.Nonempty) (h2 : BddAbove s) : sSup s ∈ s := by
  classical
  rw [csSup_eq_greatestOfBdd _ h2.choose_spec h1]
  exact (greatestOfBdd _ (Classical.choose_spec h2) h1).2.1

theorem csInf_mem {s : Set ℤ} (h1 : s.Nonempty) (h2 : BddBelow s) : sInf s ∈ s := by
  classical
  rw [csInf_eq_leastOfBdd _ h2.choose_spec h1]
  exact (leastOfBdd _ (Classical.choose_spec h2) h1).2.1

end Int

end

--  this example tests that the `Lattice ℤ` instance is computable;
-- i.e., that it is not found via the noncomputable instance in this file.
example : Lattice ℤ := inferInstance
