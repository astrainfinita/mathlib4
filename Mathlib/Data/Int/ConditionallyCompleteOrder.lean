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


open scoped Classical in
instance instConditionallyCompleteLinearOrder : ConditionallyCompleteLinearOrder ℤ where
  __ := instLinearOrder
  __ := LinearOrder.toLattice
  exists_isLUB_of_nonempty_of_bddAbove _ hn hb :=
    ⟨greatestOfBdd hb.choose hb.choose_spec hn, (isGreatest_coe_greatestOfBdd _ _ _).isLUB⟩
  exists_isGLB_of_nonempty_of_bddBelow _ hn hb :=
    ⟨leastOfBdd hb.choose hb.choose_spec hn, (isLeast_coe_leastOfBdd _ _ _).isGLB⟩

namespace Int

theorem csSup_eq_greatestOfBdd {s : Set ℤ} [DecidablePred (· ∈ s)] (b : ℤ) (Hb : ∀ z ∈ s, z ≤ b)
    (Hinh : ∃ z : ℤ, z ∈ s) : sSup s = greatestOfBdd b Hb Hinh := by
  convert (isGreatest_coe_greatestOfBdd _ _ _).isLUB.sSup_eq

@[deprecated (since := "2025-12-24")] alias csSup_eq_greatest_of_bdd := csSup_eq_greatestOfBdd

instance : NoBotOrder ℤ := ⟨fun x ↦ ⟨x - 1, (Int.sub_one_lt_of_le le_rfl).not_ge⟩⟩
instance : NoTopOrder ℤ := ⟨fun x ↦ ⟨x + 1, (Int.lt_add_one_of_le le_rfl).not_ge⟩⟩

@[simp]
theorem csSup_empty : sSup (∅ : Set ℤ) = Classical.arbitrary ℤ :=
  dif_neg (by simp)

@[deprecated (since := "2026-02-02")] alias csSup_of_not_bddAbove := sSup_of_not_bddAbove
@[deprecated (since := "2025-12-24")] alias csSup_of_not_bdd_above := csSup_of_not_bddAbove

theorem csInf_eq_leastOfBdd {s : Set ℤ} [DecidablePred (· ∈ s)] (b : ℤ) (Hb : ∀ z ∈ s, b ≤ z)
    (Hinh : ∃ z : ℤ, z ∈ s) : sInf s = leastOfBdd b Hb Hinh := by
  convert (isLeast_coe_leastOfBdd _ _ _).isGLB.sInf_eq

@[deprecated (since := "2025-12-24")] alias csInf_eq_least_of_bdd := csInf_eq_leastOfBdd

@[simp]
theorem csInf_empty : sInf (∅ : Set ℤ) = Classical.arbitrary ℤ :=
  dif_neg (by simp)

@[deprecated (since := "2026-02-02")] alias csInf_of_not_bddBelow := sInf_of_not_bddBelow
@[deprecated (since := "2025-12-24")] alias csInf_of_not_bdd_below := csInf_of_not_bddBelow

theorem csSup_mem {s : Set ℤ} (h1 : s.Nonempty) (h2 : BddAbove s) : sSup s ∈ s := by
  classical rw [csSup_eq_greatestOfBdd _ h2.choose_spec h1]
  convert (greatestOfBdd _ _ h1).2.1

theorem csInf_mem {s : Set ℤ} (h1 : s.Nonempty) (h2 : BddBelow s) : sInf s ∈ s := by
  classical rw [csInf_eq_leastOfBdd _ h2.choose_spec h1]
  convert (leastOfBdd _ _ h1).2.1

end Int
