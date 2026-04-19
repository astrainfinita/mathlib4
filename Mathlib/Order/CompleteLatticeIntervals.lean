/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.LatticeIntervals
public import Mathlib.Order.Interval.Set.OrdConnected

/-! # Subtypes of conditionally complete linear orders

In this file we give conditions on a subset of a conditionally complete linear order, to ensure that
the subtype is itself conditionally complete.

We check that an `OrdConnected` set satisfies these conditions.

## TODO

Add appropriate instances for all `Set.Ixx`. This requires a refactor that will allow different
default values for `sSup` and `sInf`.
-/

@[expose] public section

assert_not_exists Multiset

open Set

variable {ι : Sort*} {α : Type*} (s : Set α)

section OrdConnected

section ConditionallyCompleteLattice
variable [ConditionallyCompleteLattice α]

variable {s} in
@[to_dual]
lemma Subtype.preservesLUB_of_csSup_image_mem
    {t : Set s} (h_sSup : sSup ((↑) '' t : Set α) ∈ s) (ht : t.Nonempty) (h_bdd : BddAbove t) :
    PreservesLUB ((↑) : s → α) t :=
  .of_isLUB_image Subtype.coe_le_coe (by simp [h_sSup])
    (isLUB_csSup (ht.image _) ((Subtype.mono_coe _).map_bddAbove h_bdd))

/-- For a nonempty subset of a conditionally complete linear order to be a conditionally complete
linear order, it suffices that it contain the `sSup` of all its nonempty bounded-above subsets, and
the `sInf` of all its nonempty bounded-below subsets.
See note [reducible non-instances]. -/
abbrev subsetConditionallyCompleteLattice [Nonempty s]
    (Psup : ∀ ⦃x y⦄, x ∈ s → y ∈ s → x ⊔ y ∈ s)
    (Pinf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → x ⊓ y ∈ s)
    (h_Sup : ∀ {t : Set s}, t.Nonempty → BddAbove t → sSup ((↑) '' t : Set α) ∈ s)
    (h_Inf : ∀ {t : Set s}, t.Nonempty → BddBelow t → sInf ((↑) '' t : Set α) ∈ s) :
    ConditionallyCompleteLattice s where
  __ := Subtype.lattice Psup Pinf
  exists_isLUB_cond _ ht h_bdd :=
    ⟨_, (Subtype.preservesLUB_of_csSup_image_mem (h_Sup ht h_bdd) ht h_bdd).isLUB_sSup⟩
  exists_isGLB_cond _ ht h_bdd :=
    ⟨_, (Subtype.preservesGLB_of_csInf_image_mem (h_Inf ht h_bdd) ht h_bdd).isGLB_sInf⟩

/-- The `sSup` function on a nonempty `OrdConnected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-above subsets of `s`. -/
theorem sSup_within_of_ordConnected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddAbove t) : sSup ((↑) '' t : Set α) ∈ s := by
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht
  obtain ⟨B, hB⟩ : ∃ B, B ∈ upperBounds t := h_bdd
  refine hs.out c.2 B.2 ⟨?_, ?_⟩
  · exact (Subtype.mono_coe (· ∈ s)).le_csSup_image hct ⟨B, hB⟩
  · exact (Subtype.mono_coe (· ∈ s)).csSup_image_le ⟨c, hct⟩ hB

/-- The `sInf` function on a nonempty `OrdConnected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-below subsets of `s`. -/
theorem sInf_within_of_ordConnected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddBelow t) : sInf ((↑) '' t : Set α) ∈ s := by
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht
  obtain ⟨B, hB⟩ : ∃ B, B ∈ lowerBounds t := h_bdd
  refine hs.out B.2 c.2 ⟨?_, ?_⟩
  · exact (Subtype.mono_coe (· ∈ s)).le_csInf_image ⟨c, hct⟩ hB
  · exact (Subtype.mono_coe (· ∈ s)).csInf_image_le hct ⟨B, hB⟩

end ConditionallyCompleteLattice

variable [ConditionallyCompleteLinearOrder α]

/-- For a nonempty subset of a conditionally complete linear order to be a conditionally complete
linear order, it suffices that it contain the `sSup` of all its nonempty bounded-above subsets, and
the `sInf` of all its nonempty bounded-below subsets.
See note [reducible non-instances]. -/
abbrev subsetConditionallyCompleteLinearOrder [Nonempty s]
    (h_Sup : ∀ {t : Set s}, t.Nonempty → BddAbove t → sSup ((↑) '' t : Set α) ∈ s)
    (h_Inf : ∀ {t : Set s}, t.Nonempty → BddBelow t → sInf ((↑) '' t : Set α) ∈ s) :
    ConditionallyCompleteLinearOrder s where
  __ := DistribLattice.toLattice
  __ := (inferInstance : LinearOrder s)
  exists_isLUB_cond _ ht h_bdd :=
    ⟨_, (Subtype.preservesLUB_of_csSup_image_mem (h_Sup ht h_bdd) ht h_bdd).isLUB_sSup⟩
  exists_isGLB_cond _ ht h_bdd :=
    ⟨_, (Subtype.preservesGLB_of_csInf_image_mem (h_Inf ht h_bdd) ht h_bdd).isGLB_sInf⟩

/-- A nonempty `OrdConnected` set in a conditionally complete linear order is naturally a
conditionally complete linear order. -/
instance ordConnectedSubsetConditionallyCompleteLinearOrder [Nonempty s] [OrdConnected s] :
    ConditionallyCompleteLinearOrder s :=
  subsetConditionallyCompleteLinearOrder s
    (fun h => sSup_within_of_ordConnected h)
    (fun h => sInf_within_of_ordConnected h)

end OrdConnected

section Icc

/-- Conditionally complete lattice structure on `Set.Icc` -/
noncomputable instance Set.Icc.conditionallyCompleteLattice [ConditionallyCompleteLattice α]
    {a b : α} [Fact (a ≤ b)] : ConditionallyCompleteLattice (Set.Icc a b) :=
  subsetConditionallyCompleteLattice (Icc a b)
    (fun x y hx hy => (⟨x, hx⟩ ⊔ ⟨y, hy⟩ : Icc a b).2)
    (fun x y hx hy => (⟨x, hx⟩ ⊓ ⟨y, hy⟩ : Icc a b).2)
    (fun h => sSup_within_of_ordConnected h)
    (fun h => sInf_within_of_ordConnected h)

/-- Complete lattice structure on `Set.Icc` -/
noncomputable instance Set.Icc.completeLattice [ConditionallyCompleteLattice α]
    {a b : α} [Fact (a ≤ b)] : CompleteLattice (Set.Icc a b) :=
  inferInstance

/-- Complete linear order structure on `Set.Icc` -/
noncomputable instance [ConditionallyCompleteLinearOrder α] {a b : α} [Fact (a ≤ b)] :
    CompleteLinearOrder (Set.Icc a b) :=
  { Set.Icc.completeLattice, Subtype.instLinearOrder _, LinearOrder.toBiheytingAlgebra _ with }

lemma Set.Icc.coe_sSup [ConditionallyCompleteLattice α] {a b : α} (h : a ≤ b)
    {S : Set (Set.Icc a b)} (hS : S.Nonempty) : have : Fact (a ≤ b) := ⟨h⟩
    ↑(sSup S) = sSup ((↑) '' S : Set α) :=
  have : Fact (a ≤ b) := ⟨h⟩
  Subtype.preservesLUB_of_csSup_image_mem
    (sSup_within_of_ordConnected hS (OrderTop.bddAbove S)) hS (OrderTop.bddAbove S)
    |>.map_sSup

lemma Set.Icc.coe_sInf [ConditionallyCompleteLattice α] {a b : α} (h : a ≤ b)
    {S : Set (Set.Icc a b)} (hS : S.Nonempty) : have : Fact (a ≤ b) := ⟨h⟩
    ↑(sInf S) = sInf ((↑) '' S : Set α) :=
  have : Fact (a ≤ b) := ⟨h⟩
  Subtype.preservesGLB_of_csInf_image_mem
    (sInf_within_of_ordConnected hS (OrderBot.bddBelow S)) hS (OrderBot.bddBelow S)
    |>.map_sInf

lemma Set.Icc.coe_iSup [ConditionallyCompleteLattice α] {a b : α} (h : a ≤ b)
    [Nonempty ι] {S : ι → Set.Icc a b} : have : Fact (a ≤ b) := ⟨h⟩
    ↑(iSup S) = (⨆ i, S i : α) :=
  (Set.Icc.coe_sSup h (range_nonempty S)).trans (congrArg sSup (range_comp Subtype.val S).symm)

lemma Set.Icc.coe_iInf [ConditionallyCompleteLattice α] {a b : α} (h : a ≤ b)
    [Nonempty ι] {S : ι → Set.Icc a b} : have : Fact (a ≤ b) := ⟨h⟩
    ↑(iInf S) = (⨅ i, S i : α) :=
  (Set.Icc.coe_sInf h (range_nonempty S)).trans (congrArg sInf (range_comp Subtype.val S).symm)

end Icc

namespace Set.Iic

instance [ConditionallyCompleteLattice α] {a : α} : ConditionallyCompleteLattice (Iic a) :=
  subsetConditionallyCompleteLattice (Iic a)
    (fun x y hx hy => (⟨x, hx⟩ ⊔ ⟨y, hy⟩ : Iic a).2)
    (fun x y hx hy => (⟨x, hx⟩ ⊓ ⟨y, hy⟩ : Iic a).2)
    (fun h => sSup_within_of_ordConnected h)
    (fun h => sInf_within_of_ordConnected h)

variable [CompleteLattice α] {a : α}

instance instCompleteLattice : CompleteLattice (Iic a) := inferInstance

variable (S : Set <| Iic a) (f : ι → Iic a) (p : ι → Prop)

@[simp] theorem coe_sSup : (↑(sSup S) : α) = sSup ((↑) '' S) := by
  obtain rfl | hS := S.eq_empty_or_nonempty
  · simp
  · exact Subtype.preservesLUB_of_csSup_image_mem
      (sSup_within_of_ordConnected hS (OrderTop.bddAbove S)) hS (OrderTop.bddAbove S)
      |>.map_sSup

@[simp] theorem coe_iSup : (↑(⨆ i, f i) : α) = ⨆ i, (f i : α) := by
  rw [iSup, coe_sSup]; congr; ext; simp

theorem coe_biSup : (↑(⨆ i, ⨆ (_ : p i), f i) : α) = ⨆ i, ⨆ (_ : p i), (f i : α) := by simp

@[simp] theorem coe_sInf : (↑(sInf S) : α) = a ⊓ sInf ((↑) '' S) := by
  obtain rfl | hS := S.eq_empty_or_nonempty
  · simp
  · rw [inf_eq_right.mpr (hS.elim fun b hb ↦ sInf_le_of_le (mem_image_of_mem _ hb) b.2)]
    exact Subtype.preservesGLB_of_csInf_image_mem
      (sInf_within_of_ordConnected hS (OrderBot.bddBelow S)) hS (OrderBot.bddBelow S)
      |>.map_sInf

@[simp] theorem coe_iInf : (↑(⨅ i, f i) : α) = a ⊓ ⨅ i, (f i : α) := by
  rw [iInf, coe_sInf]; congr; ext; simp

theorem coe_biInf : (↑(⨅ i, ⨅ (_ : p i), f i) : α) = a ⊓ ⨅ i, ⨅ (_ : p i), (f i : α) := by
  cases isEmpty_or_nonempty ι
  · simp
  · simp_rw [coe_iInf, ← inf_iInf, ← inf_assoc, inf_idem]


end Set.Iic
