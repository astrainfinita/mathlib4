/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.PiLex
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Complete linear order instance on lexicographically ordered pi types

We show that for `α` a family of complete linear orders, the lexicographically ordered type of
dependent functions `Πₗ i, α i` is itself a complete linear order.
-/

@[expose] public section

variable {ι : Type*} {α : ι → Type*} [LinearOrder ι] [∀ i, CompleteLinearOrder (α i)]

namespace Pi

/-! ### Lexicographic ordering -/

namespace Lex
variable [WellFoundedLT ι]

private noncomputable def inf [WellFoundedLT ι] (s : Set (Πₗ i, α i)) (i : ι) : α i :=
  ⨅ e : {e ∈ s | ∀ j < i, e j = inf s j}, e.1 i
termination_by wellFounded_lt.wrap i

private theorem inf_apply (s : Set (Πₗ i, α i)) (i : ι) :
    inf s i = ⨅ e : {e ∈ s | ∀ j < i, e j = inf s j}, e.1 i := by
  simp [inf]

private theorem inf_apply_le {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (he : e ∈ s) (h : ∀ j < i, e j = inf s j) : inf s i ≤ e i := by
  rw [inf_apply]
  exact sInf_le ⟨⟨e, he, h⟩, rfl⟩

private theorem le_inf_apply {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (h : ∀ f ∈ s, (∀ j < i, f j = inf s j) → e i ≤ f i) : e i ≤ inf s i := by
  rw [inf_apply]
  apply le_sInf
  grind

private theorem isGLB_inf (s : Set (Πₗ i, α i)) : IsGLB s (toLex (inf s)) := by
  refine ⟨fun e he ↦ ?_, fun e h ↦ ?_⟩
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    exact ha.2.not_ge (inf_apply_le he ha.1)
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    refine ha.2.not_ge <| le_inf_apply fun f hf hf' ↦ apply_le_of_toLex (h hf) ?_
    simp_all

theorem sInf_apply (s : Set (Πₗ i, α i)) (i : ι) :
    sInf s i = ⨅ e : {e ∈ s | ∀ j < i, e j = sInf s j}, e.1 i :=
  (isGLB_inf s).sInf_eq ▸ inf_apply s i

theorem sInf_apply_le {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (he : e ∈ s) (h : ∀ j < i, e j = sInf s j) : sInf s i ≤ e i := by
  rw [(isGLB_inf s).sInf_eq] at h ⊢; exact inf_apply_le he h

theorem le_sInf_apply {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (h : ∀ f ∈ s, (∀ j < i, f j = sInf s j) → e i ≤ f i) : e i ≤ sInf s i := by
  rw [(isGLB_inf s).sInf_eq] at h ⊢; exact le_inf_apply h

-- TODO: figure out how to use `to_dual` here

private noncomputable def sup [WellFoundedLT ι] (s : Set (Πₗ i, α i)) : ∀ i, α i :=
  inf (α := fun i ↦ (α i)ᵒᵈ) s

private theorem sup_apply (s : Set (Πₗ i, α i)) (i : ι) :
    sup s i = ⨆ e : {e ∈ s | ∀ j < i, e j = sup s j}, e.1 i :=
  inf_apply (α := fun i ↦ (α i)ᵒᵈ) ..

private theorem le_sup_apply {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (he : e ∈ s) (h : ∀ j < i, e j = sup s j) : e i ≤ sup s i :=
  inf_apply_le (α := fun i ↦ (α i)ᵒᵈ) he h

private theorem sup_apply_le {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (h : ∀ f ∈ s, (∀ j < i, f j = sup s j) → f i ≤ e i) : sup s i ≤ e i :=
  le_inf_apply (α := fun i ↦ (α i)ᵒᵈ) h

private theorem isLUB_sup (s : Set (Πₗ i, α i)) : IsLUB s (sup s) := by
  refine ⟨fun e he ↦ ?_, fun e h ↦ ?_⟩
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    exact ha.2.not_ge (le_sup_apply he fun j hj ↦ (ha.1 j hj).symm)
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    refine ha.2.not_ge <| sup_apply_le fun f hf hf' ↦ apply_le_of_toLex (h hf) ?_
    simp_all

theorem sSup_apply (s : Set (Πₗ i, α i)) (i : ι) :
    sSup s i = ⨆ e : {e ∈ s | ∀ j < i, e j = sSup s j}, e.1 i :=
  (isLUB_sup s).sSup_eq ▸ sup_apply s i

theorem le_sSup_apply {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (he : e ∈ s) (h : ∀ j < i, e j = sSup s j) : e i ≤ sSup s i := by
  rw [(isLUB_sup s).sSup_eq] at h ⊢; exact le_sup_apply he h

theorem sSup_apply_le {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (h : ∀ f ∈ s, (∀ j < i, f j = sSup s j) → f i ≤ e i) : sSup s i ≤ e i := by
  rw [(isLUB_sup s).sSup_eq] at h ⊢; exact sup_apply_le h

noncomputable instance completeLattice : CompleteLattice (Πₗ i, α i) where
  exists_isGLB s := by exact ⟨_, isGLB_inf _⟩
  exists_isLUB s := by exact ⟨_, isLUB_sup _⟩

noncomputable instance : CompleteLinearOrder (Πₗ i, α i) where
  __ := linearOrder
  __ := completeLattice
  __ := LinearOrder.toBiheytingAlgebra _

end Lex

/-! ### Colexicographic ordering -/

namespace Colex
variable [WellFoundedGT ι]

theorem sInf_apply (s : Set (Colex ((i : ι) → α i))) (i : ι) :
    sInf s i = ⨅ e : {e ∈ s | ∀ j > i, e j = sInf s j}, e.1 i :=
  Lex.sInf_apply (ι := ιᵒᵈ) s i

theorem sInf_apply_le {s : Set (Colex ((i : ι) → α i))} {i : ι} {e : Colex ((i : ι) → α i)}
    (he : e ∈ s) (h : ∀ j > i, e j = sInf s j) : sInf s i ≤ e i :=
  Lex.sInf_apply_le (ι := ιᵒᵈ) he h

theorem le_sInf_apply {s : Set (Colex ((i : ι) → α i))} {i : ι} {e : Colex ((i : ι) → α i)}
    (h : ∀ f ∈ s, (∀ j > i, f j = sInf s j) → e i ≤ f i) : e i ≤ sInf s i :=
  Lex.le_sInf_apply (ι := ιᵒᵈ) h

-- TODO: figure out how to use `to_dual` here

theorem sSup_apply (s : Set (Colex ((i : ι) → α i))) (i : ι) :
    sSup s i = ⨆ e : {e ∈ s | ∀ j > i, e j = sSup s j}, e.1 i :=
  Lex.sSup_apply (ι := ιᵒᵈ) s i

theorem le_sSup_apply {s : Set (Colex ((i : ι) → α i))} {i : ι} {e : Colex ((i : ι) → α i)}
    (he : e ∈ s) (h : ∀ j > i, e j = sSup s j) : e i ≤ sSup s i :=
  Lex.le_sSup_apply (ι := ιᵒᵈ) he h

theorem sSup_apply_le {s : Set (Colex ((i : ι) → α i))} {i : ι} {e : Colex ((i : ι) → α i)}
    (h : ∀ f ∈ s, (∀ j > i, f j = sSup s j) → f i ≤ e i) : sSup s i ≤ e i :=
  Lex.sSup_apply_le (ι := ιᵒᵈ) h

set_option backward.isDefEq.respectTransparency false in
noncomputable instance completeLattice : CompleteLattice (Colex ((i : ι) → α i)) where
  exists_isLUB _ := by exact ⟨_, Lex.isLUB_sup (ι := ιᵒᵈ) _⟩
  exists_isGLB _ := by exact ⟨_, Lex.isGLB_inf (ι := ιᵒᵈ) _⟩

noncomputable instance : CompleteLinearOrder (Colex ((i : ι) → α i)) where
  __ := linearOrder
  __ := completeLattice
  __ := LinearOrder.toBiheytingAlgebra _

end Colex
end Pi
