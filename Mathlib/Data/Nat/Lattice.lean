/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Gabriel Ebner, Yury Kudryashov
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Conditionally complete linear order structure on `ℕ`

In this file we

* define a `ConditionallyCompleteLinearOrderBot` structure on `ℕ`;
* prove a few lemmas about `iSup`/`iInf`/`Set.iUnion`/`Set.iInter` and natural numbers.
-/

@[expose] public section

assert_not_exists MonoidWithZero

open Set

namespace Nat

open scoped Classical in
theorem sInf_def {s : Set ℕ} (h : s.Nonempty) : sInf s = @Nat.find (fun n ↦ n ∈ s) _ h :=
  (Nat.isLeast_find h).isGLB.sInf_eq

open scoped Classical in
theorem sSup_def {s : Set ℕ} (h : ∃ n, ∀ a ∈ s, a ≤ n) :
    sSup s = @Nat.find (fun n ↦ ∀ a ∈ s, a ≤ n) _ h :=
  IsLUB.sSup_eq (Nat.isLeast_find h)

theorem sSup_of_not_bddAbove {s : Set ℕ} (h : ¬BddAbove s) : sSup s = Classical.arbitrary ℕ :=
  _root_.sSup_of_not_bddAbove h

lemma iSup_of_not_bddAbove {ι : Sort*} {f : ι → ℕ} (h : ¬ BddAbove (Set.range f)) :
    (⨆ i, f i : ℕ) = Classical.arbitrary ℕ := Nat.sSup_of_not_bddAbove h

theorem _root_.Set.Infinite.Nat.sSup_eq {s : Set ℕ} (h : s.Infinite) :
    sSup s = Classical.arbitrary ℕ :=
  sSup_of_not_bddAbove h.not_bddAbove

@[deprecated (since := "2026-04-06")]
alias _root_.Set.Infinite.Nat.sSup_eq_zero := Set.Infinite.Nat.sSup_eq

@[simp]
theorem sInf_eq_zero {s : Set ℕ} (h : s.Nonempty) : sInf s = 0 ↔ 0 ∈ s := by
  simp only [Nat.sInf_def, h, Nat.find_eq_zero]

theorem sInf_empty : sInf ∅ = Classical.arbitrary ℕ :=
  NoTopOrder.sInf_empty

@[simp]
theorem iInf_of_empty {ι : Sort*} [IsEmpty ι] (f : ι → ℕ) : iInf f = Classical.arbitrary ℕ := by
  rw [iInf_of_isEmpty, sInf_empty]

-- Old statement before `sInf` refactor: `⨅ _ : ι, 0 = 0`
@[deprecated "Use `ciInf_const` or `Nat.iInf_of_empty` instead" (since := "2026-04-06")]
lemma iInf_const_zero {ι : Sort*} : ⨅ _ : ι, 0 = 0 ∨ ⨅ _ : ι, 0 = Classical.arbitrary ℕ :=
  (isEmpty_or_nonempty ι).elim (fun h ↦ by simp)
    fun h ↦ .inl <| (sInf_eq_zero (by simp)).2 <| by simp

theorem sInf_mem {s : Set ℕ} (h : s.Nonempty) : sInf s ∈ s := by
  classical
  rw [Nat.sInf_def h]
  exact Nat.find_spec h

theorem notMem_of_lt_sInf {s : Set ℕ} {m : ℕ} (hm : m < sInf s) : m ∉ s := by
  classical
  cases eq_empty_or_nonempty s with
  | inl h => subst h; apply notMem_empty
  | inr h => rw [Nat.sInf_def h] at hm; exact Nat.find_min h hm

protected theorem sInf_le {s : Set ℕ} {m : ℕ} (hm : m ∈ s) : sInf s ≤ m := by
  classical
  rw [Nat.sInf_def ⟨m, hm⟩]
  exact Nat.find_min' ⟨m, hm⟩ hm

@[deprecated "Old statement before `sInf` refactor: `0 < sInf s → s.Nonempty`"
  (since := "2026-04-06")]
theorem nonempty_of_pos_sInf {s : Set ℕ} (h : sInf s ≠ Classical.arbitrary ℕ) : s.Nonempty := by
  contrapose! h; exact h ▸ sInf_empty

set_option linter.deprecated false in
@[deprecated "Old statement before `sInf` refactor: `sInf s = k + 1 → s.Nonempty`"
  (since := "2026-04-06")]
theorem nonempty_of_sInf_eq_succ {s : Set ℕ} (h : sInf s ≠ Classical.arbitrary ℕ) : s.Nonempty :=
  nonempty_of_pos_sInf h

theorem eq_Ici_of_nonempty_of_upward_closed {s : Set ℕ} (hs : s.Nonempty)
    (hs' : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s) : s = Ici (sInf s) :=
  ext fun n ↦ ⟨fun H ↦ Nat.sInf_le H, fun H ↦ hs' (sInf s) n H (sInf_mem hs)⟩

theorem sInf_upward_closed_eq_succ_iff {s : Set ℕ} (hn : s.Nonempty)
    (hs : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s) (k : ℕ) :
    sInf s = k + 1 ↔ k + 1 ∈ s ∧ k ∉ s := by
  classical
  constructor
  · intro H
    rw [eq_Ici_of_nonempty_of_upward_closed hn hs, H, mem_Ici, mem_Ici]
    exact ⟨le_rfl, k.not_succ_le_self⟩
  · rintro ⟨H, H'⟩
    rw [sInf_def (⟨_, H⟩ : s.Nonempty), find_eq_iff]
    exact ⟨H, fun n hnk hns ↦ H' <| hs n k (Nat.lt_succ_iff.mp hnk) hns⟩

/-- This instance is necessary, otherwise the lattice operations would be derived via
`ConditionallyCompleteLinearOrderBot` and marked as noncomputable. -/
instance : Lattice ℕ :=
  LinearOrder.toLattice

open scoped Classical in
noncomputable instance : ConditionallyCompleteLinearOrderBot ℕ :=
  { (inferInstance : OrderBot ℕ), (LinearOrder.toLattice : Lattice ℕ),
    (inferInstance : LinearOrder ℕ) with
    exists_isLUB_cond _ _ hb := ⟨_, Nat.isLeast_find hb⟩
    exists_isGLB_cond _ hn _ := ⟨_, (Nat.isLeast_find hn).isGLB⟩ }

theorem sSup_mem {s : Set ℕ} (h₁ : s.Nonempty) (h₂ : BddAbove s) : sSup s ∈ s :=
  let ⟨k, hk⟩ := h₂
  h₁.csSup_mem ((finite_le_nat k).subset hk)

theorem sInf_add {n : ℕ} {p : ℕ → Prop} (hpn : ∃ m ≥ n, p m) (hn : n ≤ sInf { m | p m }) :
    sInf { m | p (m + n) } + n = sInf { m | p m } := by
  classical
  obtain ⟨_, hmn, hm⟩ := hpn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hmn
  have hp : ∃ n, n ∈ { m | p m } := ⟨_, hm⟩
  rw [Nat.sInf_def ⟨m, hm⟩, Nat.sInf_def hp]
  rw [Nat.sInf_def hp] at hn
  exact find_add hn

theorem sInf_add' {n : ℕ} {p : ℕ → Prop} (hp : { m | p m }.Nonempty) (h : 0 < sInf { m | p m }) :
    sInf { m | p m } + n = sInf { m | p (m - n) } := by
  obtain ⟨m, hm⟩ := hp
  suffices h₁ : n ≤ sInf {m | p (m - n)} by
    convert sInf_add ⟨m + n, le_add_left _ _, by rwa [Nat.add_sub_cancel_right]⟩ h₁
    simp_rw [Nat.add_sub_cancel_right]
  refine
    le_csInf ⟨m + n, ?_⟩ fun b hb ↦
      le_of_not_gt fun hbn ↦
        ne_of_mem_of_not_mem ?_ (notMem_of_lt_sInf h) (Nat.sub_eq_zero_of_le hbn.le)
  · dsimp
    rwa [Nat.add_sub_cancel_right]
  · exact hb

section

variable {α : Type*} [CompleteLattice α]

theorem iSup_lt_succ (u : ℕ → α) (n : ℕ) : ⨆ k < n + 1, u k = (⨆ k < n, u k) ⊔ u n := by
  simp_rw [Nat.lt_add_one_iff, biSup_le_eq_sup]

theorem iSup_lt_succ' (u : ℕ → α) (n : ℕ) : ⨆ k < n + 1, u k = u 0 ⊔ ⨆ k < n, u (k + 1) := by
  rw [← sup_iSup_nat_succ]
  simp

theorem iInf_lt_succ (u : ℕ → α) (n : ℕ) : ⨅ k < n + 1, u k = (⨅ k < n, u k) ⊓ u n :=
  @iSup_lt_succ αᵒᵈ _ _ _

theorem iInf_lt_succ' (u : ℕ → α) (n : ℕ) : ⨅ k < n + 1, u k = u 0 ⊓ ⨅ k < n, u (k + 1) :=
  @iSup_lt_succ' αᵒᵈ _ _ _

theorem iSup_le_succ (u : ℕ → α) (n : ℕ) : ⨆ k ≤ n + 1, u k = (⨆ k ≤ n, u k) ⊔ u (n + 1) := by
  simp_rw [← Nat.lt_succ_iff, iSup_lt_succ]

theorem iSup_le_succ' (u : ℕ → α) (n : ℕ) : ⨆ k ≤ n + 1, u k = u 0 ⊔ ⨆ k ≤ n, u (k + 1) := by
  simp_rw [← Nat.lt_succ_iff, iSup_lt_succ']

theorem iInf_le_succ (u : ℕ → α) (n : ℕ) : ⨅ k ≤ n + 1, u k = (⨅ k ≤ n, u k) ⊓ u (n + 1) :=
  @iSup_le_succ αᵒᵈ _ _ _

theorem iInf_le_succ' (u : ℕ → α) (n : ℕ) : ⨅ k ≤ n + 1, u k = u 0 ⊓ ⨅ k ≤ n, u (k + 1) :=
  @iSup_le_succ' αᵒᵈ _ _ _

end

end Nat

namespace Set

variable {α : Type*}

theorem biUnion_lt_succ (u : ℕ → Set α) (n : ℕ) : ⋃ k < n + 1, u k = (⋃ k < n, u k) ∪ u n :=
  Nat.iSup_lt_succ u n

theorem biUnion_lt_succ' (u : ℕ → Set α) (n : ℕ) : ⋃ k < n + 1, u k = u 0 ∪ ⋃ k < n, u (k + 1) :=
  Nat.iSup_lt_succ' u n

theorem biInter_lt_succ (u : ℕ → Set α) (n : ℕ) : ⋂ k < n + 1, u k = (⋂ k < n, u k) ∩ u n :=
  Nat.iInf_lt_succ u n

theorem biInter_lt_succ' (u : ℕ → Set α) (n : ℕ) : ⋂ k < n + 1, u k = u 0 ∩ ⋂ k < n, u (k + 1) :=
  Nat.iInf_lt_succ' u n

theorem biUnion_le_succ (u : ℕ → Set α) (n : ℕ) : ⋃ k ≤ n + 1, u k = (⋃ k ≤ n, u k) ∪ u (n + 1) :=
  Nat.iSup_le_succ u n

theorem biUnion_le_succ' (u : ℕ → Set α) (n : ℕ) : ⋃ k ≤ n + 1, u k = u 0 ∪ ⋃ k ≤ n, u (k + 1) :=
  Nat.iSup_le_succ' u n

theorem biInter_le_succ (u : ℕ → Set α) (n : ℕ) : ⋂ k ≤ n + 1, u k = (⋂ k ≤ n, u k) ∩ u (n + 1) :=
  Nat.iInf_le_succ u n

theorem biInter_le_succ' (u : ℕ → Set α) (n : ℕ) : ⋂ k ≤ n + 1, u k = u 0 ∩ ⋂ k ≤ n, u (k + 1) :=
  Nat.iInf_le_succ' u n

end Set
