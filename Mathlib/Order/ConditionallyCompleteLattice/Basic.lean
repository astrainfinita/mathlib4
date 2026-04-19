/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompletePartialOrder.Basic
public import Mathlib.Order.Bounds.WithBot

/-!
# Theory of conditionally complete lattices

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

-- Guard against import creep
assert_not_exists Multiset

open Function OrderDual Set

variable {α β γ : Type*} {ι : Sort*}

instance ConditionallyCompleteLinearOrder.toLinearOrder [h : ConditionallyCompleteLinearOrder α] :
    LinearOrder α where
  min_def a b := by
    by_cases hab : a = b
    · simp [hab]
    · rcases ConditionallyCompleteLinearOrder.le_total a b with (h₁ | h₂)
      · simp [h₁]
      · simp [show ¬(a ≤ b) from fun h => hab (le_antisymm h h₂), h₂]
  max_def a b := by
    by_cases hab : a = b
    · simp [hab]
    · rcases ConditionallyCompleteLinearOrder.le_total a b with (h₁ | h₂)
      · simp [h₁]
      · simp [show ¬(a ≤ b) from fun h => hab (le_antisymm h h₂), h₂]
  __ := h

-- see Note [lower instance priority]
attribute [instance 100] ConditionallyCompleteLinearOrderBot.toOrderBot

-- see Note [lower instance priority]
/-- A complete lattice is a conditionally complete lattice, as there are no restrictions
on the properties of sInf and sSup in a complete lattice. -/
instance (priority := 100) CompleteLattice.toConditionallyCompleteLattice [CompleteLattice α] :
    ConditionallyCompleteLattice α where
  exists_isLUB_cond _ _ _ := ⟨_, isLUB_sSup _⟩
  exists_isGLB_cond _ _ _ := ⟨_, isGLB_sInf _⟩

-- see Note [lower instance priority]
instance (priority := 100) CompleteLinearOrder.toConditionallyCompleteLinearOrderBot {α : Type*}
    [h : CompleteLinearOrder α] : ConditionallyCompleteLinearOrderBot α where
  __ := CompleteLattice.toConditionallyCompleteLattice
  __ := h

namespace OrderDual

instance instConditionallyCompleteLattice (α : Type*) [ConditionallyCompleteLattice α] :
    ConditionallyCompleteLattice αᵒᵈ where
  exists_isLUB_cond := ConditionallyCompleteLattice.exists_isGLB_cond (α := α)
  exists_isGLB_cond := ConditionallyCompleteLattice.exists_isLUB_cond (α := α)

instance (α : Type*) [ConditionallyCompleteLinearOrder α] :
    ConditionallyCompleteLinearOrder αᵒᵈ where
  __ := OrderDual.instConditionallyCompleteLattice α
  __ := OrderDual.instLinearOrder α

end OrderDual

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {s t : Set α} {a b : α}

@[to_dual]
theorem isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s := by bddDefault) : IsLUB s (sSup s) :=
  isLUB_sSup_of_exists (ConditionallyCompleteLattice.exists_isLUB_cond s hn hb)

@[to_dual]
theorem exists_isLUB_of_nonempty_of_bddAbove (hn : s.Nonempty) (hb : BddAbove s := by bddDefault) :
    ∃ a, IsLUB s a := by
  obtain _ | _ := isEmpty_or_nonempty α
  · exact hn.elim fun a _ ↦ isEmptyElim a
  · exact ⟨sSup s, isLUB_csSup hn hb⟩

@[to_dual csInf_le]
theorem le_csSup (h₁ : BddAbove s) (h₂ : a ∈ s) : a ≤ sSup s :=
  (isLUB_csSup (nonempty_of_mem h₂) h₁).1 h₂

@[to_dual le_csInf]
theorem csSup_le (h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, b ≤ a) : sSup s ≤ a :=
  (isLUB_csSup h₁ ⟨a, h₂⟩).2 h₂

theorem le_csSup_of_le (hs : BddAbove s) (hb : b ∈ s) (h : a ≤ b) : a ≤ sSup s :=
  le_trans h (le_csSup hs hb)

theorem csInf_le_of_le (hs : BddBelow s) (hb : b ∈ s) (h : b ≤ a) : sInf s ≤ a :=
  le_trans (csInf_le hs hb) h

@[gcongr low]
theorem csSup_le_csSup (ht : BddAbove t) (hs : s.Nonempty) (h : s ⊆ t) : sSup s ≤ sSup t :=
  csSup_le hs fun _ ha => le_csSup ht (h ha)

@[gcongr low]
theorem csInf_le_csInf (ht : BddBelow t) (hs : s.Nonempty) (h : s ⊆ t) : sInf t ≤ sInf s :=
  le_csInf hs fun _ ha => csInf_le ht (h ha)

theorem le_csSup_iff (h : BddAbove s) (hs : s.Nonempty) :
    a ≤ sSup s ↔ ∀ b, b ∈ upperBounds s → a ≤ b :=
  ⟨fun h _ hb => le_trans h (csSup_le hs hb), fun hb => hb _ fun _ => le_csSup h⟩

theorem csInf_le_iff (h : BddBelow s) (hs : s.Nonempty) : sInf s ≤ a ↔ ∀ b ∈ lowerBounds s, b ≤ a :=
  ⟨fun h _ hb => le_trans (le_csInf hs hb) h, fun hb => hb _ fun _ => csInf_le h⟩

@[to_dual]
theorem IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup s = a :=
  (isLUB_csSup ne ⟨a, H.1⟩).unique H

instance (priority := 100) ConditionallyCompleteLattice.toConditionallyCompletePartialOrder :
    ConditionallyCompletePartialOrder α where
  exists_isLUB_cond_of_directed _ _ hn hb := ⟨_, isLUB_csSup hn hb⟩
  exists_isGLB_cond_of_directed _ _ hn hb := ⟨_, isGLB_csInf hn hb⟩

theorem subset_Icc_csInf_csSup (hb : BddBelow s) (ha : BddAbove s) : s ⊆ Icc (sInf s) (sSup s) :=
  fun _ hx => ⟨csInf_le hb hx, le_csSup ha hx⟩

theorem csSup_le_iff (hb : BddAbove s) (hs : s.Nonempty) : sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (isLUB_csSup hs hb)

theorem le_csInf_iff (hb : BddBelow s) (hs : s.Nonempty) : a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b :=
  le_isGLB_iff (isGLB_csInf hs hb)

theorem csSup_lowerBounds_eq_csInf {s : Set α} (h : BddBelow s) (hs : s.Nonempty) :
    sSup (lowerBounds s) = sInf s :=
  (isLUB_csSup h <| hs.mono fun _ hx _ hy => hy hx).unique (isGLB_csInf hs h).isLUB

theorem csInf_upperBounds_eq_csSup {s : Set α} (h : BddAbove s) (hs : s.Nonempty) :
    sInf (upperBounds s) = sSup s :=
  (isGLB_csInf h <| hs.mono fun _ hx _ hy => hy hx).unique (isLUB_csSup hs h).isGLB

theorem csSup_lowerBounds_range [Nonempty β] {f : β → α} (hf : BddBelow (range f)) :
    sSup (lowerBounds (range f)) = ⨅ i, f i :=
  csSup_lowerBounds_eq_csInf hf <| range_nonempty _

theorem csInf_upperBounds_range [Nonempty β] {f : β → α} (hf : BddAbove (range f)) :
    sInf (upperBounds (range f)) = ⨆ i, f i :=
  csInf_upperBounds_eq_csSup hf <| range_nonempty _

theorem notMem_of_lt_csInf {x : α} {s : Set α} (h : x < sInf s) (hs : BddBelow s) : x ∉ s :=
  fun hx => lt_irrefl _ (h.trans_le (csInf_le hs hx))

theorem notMem_of_csSup_lt {x : α} {s : Set α} (h : sSup s < x) (hs : BddAbove s) : x ∉ s :=
  notMem_of_lt_csInf (α := αᵒᵈ) h hs

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w<b`.
See `sSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem csSup_eq_of_forall_le_of_forall_lt_exists_gt (hs : s.Nonempty) (H : ∀ a ∈ s, a ≤ b)
    (H' : ∀ w, w < b → ∃ a ∈ s, w < a) : sSup s = b :=
  (eq_of_le_of_not_lt (csSup_le hs H)) fun hb =>
    let ⟨_, ha, ha'⟩ := H' _ hb
    lt_irrefl _ <| ha'.trans_le <| le_csSup ⟨b, H⟩ ha

/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w>b`.
See `sInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem csInf_eq_of_forall_ge_of_forall_gt_exists_lt :
    s.Nonempty → (∀ a ∈ s, b ≤ a) → (∀ w, b < w → ∃ a ∈ s, a < w) → sInf s = b :=
  csSup_eq_of_forall_le_of_forall_lt_exists_gt (α := αᵒᵈ)

/-- `b < sSup s` when there is an element `a` in `s` with `b < a`, when `s` is bounded above.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness above for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the `CompleteLattice` case. -/
theorem lt_csSup_of_lt (hs : BddAbove s) (ha : a ∈ s) (h : b < a) : b < sSup s :=
  lt_of_lt_of_le h (le_csSup hs ha)

/-- `sInf s < b` when there is an element `a` in `s` with `a < b`, when `s` is bounded below.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness below for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the `CompleteLattice` case. -/
theorem csInf_lt_of_lt : BddBelow s → a ∈ s → a < b → sInf s < b :=
  lt_csSup_of_lt (α := αᵒᵈ)

/-- If all elements of a nonempty set `s` are less than or equal to all elements
of a nonempty set `t`, then there exists an element between these sets. -/
theorem exists_between_of_forall_le (sne : s.Nonempty) (tne : t.Nonempty)
    (hst : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) : (upperBounds s ∩ lowerBounds t).Nonempty :=
  ⟨sInf t, fun x hx => le_csInf tne <| hst x hx, fun _ hy => csInf_le (sne.mono hst) hy⟩

theorem csSup_pair (a b : α) : sSup {a, b} = a ⊔ b :=
  (@isLUB_pair _ _ a b).csSup_eq (insert_nonempty _ _)

theorem csInf_pair (a b : α) : sInf {a, b} = a ⊓ b :=
  (@isGLB_pair _ _ a b).csInf_eq (insert_nonempty _ _)

/-- If a set is bounded below and above, and nonempty, its infimum is less than or equal to
its supremum. -/
theorem csInf_le_csSup (ne : s.Nonempty) (hb : BddBelow s := by bddDefault)
    (ha : BddAbove s := by bddDefault) : sInf s ≤ sSup s :=
  isGLB_le_isLUB (isGLB_csInf ne hb) (isLUB_csSup ne ha) ne

theorem csInf_le_csSup_of_nonempty_inter (h : (s ∩ t).Nonempty) (hs : BddBelow s := by bddDefault)
    (ht : BddAbove t := by bddDefault) : sInf s ≤ sSup t :=
  isGLB_le_isLUB_of_nonempty_inter h (isGLB_csInf h.left hs) (isLUB_csSup h.right ht)

/-- The `sSup` of a union of two sets is the max of the suprema of each subset, under the
assumptions that all sets are bounded above and nonempty. -/
theorem csSup_union (hs : BddAbove s) (sne : s.Nonempty) (ht : BddAbove t) (tne : t.Nonempty) :
    sSup (s ∪ t) = sSup s ⊔ sSup t :=
  ((isLUB_csSup sne hs).union (isLUB_csSup tne ht)).csSup_eq sne.inl

/-- The `sInf` of a union of two sets is the min of the infima of each subset, under the assumptions
that all sets are bounded below and nonempty. -/
theorem csInf_union (hs : BddBelow s) (sne : s.Nonempty) (ht : BddBelow t) (tne : t.Nonempty) :
    sInf (s ∪ t) = sInf s ⊓ sInf t :=
  csSup_union (α := αᵒᵈ) hs sne ht tne

/-- The supremum of an intersection of two sets is bounded by the minimum of the suprema of each
set, if all sets are bounded above and nonempty. -/
theorem csSup_inter_le (hs : BddAbove s) (ht : BddAbove t) (hst : (s ∩ t).Nonempty) :
    sSup (s ∩ t) ≤ sSup s ⊓ sSup t :=
  (csSup_le hst) fun _ hx => le_inf (le_csSup hs hx.1) (le_csSup ht hx.2)

/-- The infimum of an intersection of two sets is bounded below by the maximum of the
infima of each set, if all sets are bounded below and nonempty. -/
theorem le_csInf_inter :
    BddBelow s → BddBelow t → (s ∩ t).Nonempty → sInf s ⊔ sInf t ≤ sInf (s ∩ t) :=
  csSup_inter_le (α := αᵒᵈ)

/-- The supremum of `insert a s` is the maximum of `a` and the supremum of `s`, if `s` is
nonempty and bounded above. -/
@[simp]
theorem csSup_insert (hs : BddAbove s) (sne : s.Nonempty) : sSup (insert a s) = a ⊔ sSup s :=
  ((isLUB_csSup sne hs).insert a).csSup_eq (insert_nonempty a s)

/-- The infimum of `insert a s` is the minimum of `a` and the infimum of `s`, if `s` is
nonempty and bounded below. -/
@[simp]
theorem csInf_insert (hs : BddBelow s) (sne : s.Nonempty) : sInf (insert a s) = a ⊓ sInf s :=
  csSup_insert (α := αᵒᵈ) hs sne

@[simp]
theorem csInf_Ioc [DenselyOrdered α] (h : a < b) : sInf (Ioc a b) = a :=
  (isGLB_Ioc h).csInf_eq (nonempty_Ioc.2 h)

@[simp]
theorem csInf_Ioi [NoMaxOrder α] [DenselyOrdered α] : sInf (Ioi a) = a :=
  csInf_eq_of_forall_ge_of_forall_gt_exists_lt nonempty_Ioi (fun _ => le_of_lt) fun w hw => by
    simpa using exists_between hw

@[simp]
theorem csInf_Ioo [DenselyOrdered α] (h : a < b) : sInf (Ioo a b) = a :=
  (isGLB_Ioo h).csInf_eq (nonempty_Ioo.2 h)

@[simp]
theorem csSup_Ico [DenselyOrdered α] (h : a < b) : sSup (Ico a b) = b :=
  (isLUB_Ico h).csSup_eq (nonempty_Ico.2 h)

@[simp]
theorem csSup_Iio [NoMinOrder α] [DenselyOrdered α] : sSup (Iio a) = a :=
  csSup_eq_of_forall_le_of_forall_lt_exists_gt nonempty_Iio (fun _ => le_of_lt) fun w hw => by
    simpa [and_comm] using exists_between hw

@[simp]
theorem csSup_Ioo [DenselyOrdered α] (h : a < b) : sSup (Ioo a b) = b :=
  (isLUB_Ioo h).csSup_eq (nonempty_Ioo.2 h)

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that
1) `b` is an upper bound
2) every other upper bound `b'` satisfies `b ≤ b'`. -/
theorem csSup_eq_of_is_forall_le_of_forall_le_imp_ge (hs : s.Nonempty) (h_is_ub : ∀ a ∈ s, a ≤ b)
    (h_b_le_ub : ∀ ub, (∀ a ∈ s, a ≤ ub) → b ≤ ub) : sSup s = b :=
  (csSup_le hs h_is_ub).antisymm ((h_b_le_ub _) fun _ => le_csSup ⟨b, h_is_ub⟩)

@[to_dual]
theorem csInf_eq_bot_of_bot_mem [OrderBot α] {s : Set α} (hs : ⊥ ∈ s) : sInf s = ⊥ :=
  eq_bot_iff.2 <| csInf_le (OrderBot.bddBelow s) hs

end ConditionallyCompleteLattice

instance Pi.conditionallyCompleteLattice {ι : Type*} {α : ι → Type*}
    [∀ i, ConditionallyCompleteLattice (α i)] : ConditionallyCompleteLattice (∀ i, α i) where
  exists_isLUB_cond _ hn hb := ⟨_,
    isLUB_pi.mpr fun _ ↦ isLUB_csSup (image_nonempty.mpr hn) ((monotone_eval _).map_bddAbove hb)⟩
  exists_isGLB_cond _ hn hb := ⟨_,
    isGLB_pi.mpr fun _ ↦ isGLB_csInf (image_nonempty.mpr hn) ((monotone_eval _).map_bddBelow hb)⟩

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {f : ι → α} {s : Set α} {a b : α}

/-- When `b < sSup s`, there is an element `a` in `s` with `b < a`, if `s` is nonempty and the order
is a linear order. -/
theorem exists_lt_of_lt_csSup (hs : s.Nonempty) (hb : b < sSup s) : ∃ a ∈ s, b < a := by
  contrapose! hb
  exact csSup_le hs hb

/-- When `sInf s < b`, there is an element `a` in `s` with `a < b`, if `s` is nonempty and the order
is a linear order. -/
theorem exists_lt_of_csInf_lt (hs : s.Nonempty) (hb : sInf s < b) : ∃ a ∈ s, a < b :=
  exists_lt_of_lt_csSup (α := αᵒᵈ) hs hb

theorem lt_csSup_iff (hb : BddAbove s) (hs : s.Nonempty) : a < sSup s ↔ ∃ b ∈ s, a < b :=
  lt_isLUB_iff <| isLUB_csSup hs hb

theorem csInf_lt_iff (hb : BddBelow s) (hs : s.Nonempty) : sInf s < a ↔ ∃ b ∈ s, b < a :=
  isGLB_lt_iff <| isGLB_csInf hs hb

@[deprecated (since := "2026-03-30")] alias csSup_of_not_bddAbove := sSup_of_not_bddAbove
@[deprecated (since := "2026-03-30")] alias ciSup_of_not_bddAbove := iSup_of_not_bddAbove

lemma csSup_eq_univ_of_not_bddAbove (hs : ¬BddAbove s) : sSup s = sSup univ := by
  rw [sSup_of_not_bddAbove hs, sSup_of_not_bddAbove (s := univ)]
  contrapose hs
  exact hs.mono (subset_univ _)

lemma ciSup_eq_univ_of_not_bddAbove (hf : ¬BddAbove (range f)) : ⨆ i, f i = sSup univ :=
  csSup_eq_univ_of_not_bddAbove hf

@[deprecated (since := "2026-03-30")] alias csInf_of_not_bddBelow := sInf_of_not_bddBelow
@[deprecated (since := "2026-03-30")] alias ciInf_of_not_bddBelow := iInf_of_not_bddBelow

lemma csInf_eq_univ_of_not_bddBelow (hs : ¬BddBelow s) : sInf s = sInf univ :=
  csSup_eq_univ_of_not_bddAbove (α := αᵒᵈ) hs

lemma ciInf_eq_univ_of_not_bddBelow (hf : ¬BddBelow (range f)) : ⨅ i, f i = sInf univ :=
  csInf_eq_univ_of_not_bddBelow hf

/-- When every element of a set `s` is bounded by an element of a set `t`, and conversely, then
`s` and `t` have the same supremum. This holds even when the sets may be empty or unbounded. -/
theorem csSup_eq_csSup_of_forall_exists_le {s t : Set α}
    (hs : ∀ x ∈ s, ∃ y ∈ t, x ≤ y) (ht : ∀ y ∈ t, ∃ x ∈ s, y ≤ x) :
    sSup s = sSup t := by
  rcases eq_empty_or_nonempty s with rfl | s_ne
  · have : t = ∅ := eq_empty_of_forall_notMem (fun y yt ↦ by simpa using ht y yt)
    rw [this]
  rcases eq_empty_or_nonempty t with rfl | t_ne
  · have : s = ∅ := eq_empty_of_forall_notMem (fun x xs ↦ by simpa using hs x xs)
    rw [this]
  by_cases B : BddAbove s ∨ BddAbove t
  · have Bs : BddAbove s := by
      rcases B with hB | ⟨b, hb⟩
      · exact hB
      · refine ⟨b, fun x hx ↦ ?_⟩
        rcases hs x hx with ⟨y, hy, hxy⟩
        exact hxy.trans (hb hy)
    have Bt : BddAbove t := by
      rcases B with ⟨b, hb⟩ | hB
      · refine ⟨b, fun y hy ↦ ?_⟩
        rcases ht y hy with ⟨x, hx, hyx⟩
        exact hyx.trans (hb hx)
      · exact hB
    apply le_antisymm
    · apply csSup_le s_ne (fun x hx ↦ ?_)
      rcases hs x hx with ⟨y, yt, hxy⟩
      exact hxy.trans (le_csSup Bt yt)
    · apply csSup_le t_ne (fun y hy ↦ ?_)
      rcases ht y hy with ⟨x, xs, hyx⟩
      exact hyx.trans (le_csSup Bs xs)
  · simp [sSup_of_not_bddAbove, (not_or.1 B).1, (not_or.1 B).2]

/-- When every element of a set `s` is bounded by an element of a set `t`, and conversely, then
`s` and `t` have the same infimum. This holds even when the sets may be empty or unbounded. -/
theorem csInf_eq_csInf_of_forall_exists_le {s t : Set α}
    (hs : ∀ x ∈ s, ∃ y ∈ t, y ≤ x) (ht : ∀ y ∈ t, ∃ x ∈ s, x ≤ y) :
    sInf s = sInf t :=
  csSup_eq_csSup_of_forall_exists_le (α := αᵒᵈ) hs ht

lemma sSup_iUnion_Iic (f : ι → α) : sSup (⋃ (i : ι), Iic (f i)) = ⨆ i, f i := by
  apply csSup_eq_csSup_of_forall_exists_le
  · simp only [mem_iUnion]
    rintro x ⟨i, hi⟩
    exact ⟨f i, mem_range_self _, hi⟩
  · rintro x ⟨i, rfl⟩
    exact ⟨f i, mem_iUnion_of_mem i le_rfl, le_rfl⟩

lemma sInf_iUnion_Ici (f : ι → α) : sInf (⋃ (i : ι), Ici (f i)) = ⨅ i, f i :=
  sSup_iUnion_Iic (α := αᵒᵈ) f

open Function

variable [WellFoundedLT α]

theorem sInf_eq_argmin_on (hs : s.Nonempty) : sInf s = argminOn id s hs :=
  IsLeast.csInf_eq ⟨argminOn_mem _ _ _, fun _ ha => argminOn_le id _ ha⟩

theorem isLeast_csInf (hs : s.Nonempty) : IsLeast s (sInf s) := by
  rw [sInf_eq_argmin_on hs]
  exact ⟨argminOn_mem _ _ _, fun a ha => argminOn_le id _ ha⟩

theorem le_csInf_iff' (hs : s.Nonempty) : b ≤ sInf s ↔ b ∈ lowerBounds s :=
  le_isGLB_iff (isLeast_csInf hs).isGLB

theorem csInf_mem (hs : s.Nonempty) : sInf s ∈ s :=
  (isLeast_csInf hs).1

lemma csInf_eq_iff (hs : s.Nonempty) (n : α) :
     sInf s = n ↔ n ∈ s ∧ ∀ a ∈ s, n ≤ a := by
  have : OrderBot α := WellFoundedLT.toOrderBot α
  constructor
  · intro rfl
    exact ⟨csInf_mem hs, fun _ ↦ csInf_le (OrderBot.bddBelow s)⟩
  · intro ⟨hn, hle⟩
    exact le_antisymm (csInf_le (OrderBot.bddBelow s) hn) (le_csInf hs hle)

theorem MonotoneOn.map_csInf {β : Type*} [ConditionallyCompleteLattice β] {f : α → β}
    (hf : MonotoneOn f s) (hs : s.Nonempty) : f (sInf s) = sInf (f '' s) :=
  (hf.map_isLeast (isLeast_csInf hs)).csInf_eq.symm

theorem Monotone.map_csInf {β : Type*} [ConditionallyCompleteLattice β] {f : α → β}
    (hf : Monotone f) (hs : s.Nonempty) : f (sInf s) = sInf (f '' s) :=
  (hf.map_isLeast (isLeast_csInf hs)).csInf_eq.symm

end ConditionallyCompleteLinearOrder

/-!
### Lemmas about a conditionally complete lattice with bottom element

In this case we have `Sup ∅ = ⊥`, so we can drop some `Nonempty`/`Set.Nonempty` assumptions.
-/


section

variable [ConditionallyCompleteLattice α] [OrderBot α] {s : Set α} {a : α}

@[to_dual]
theorem OrderBot.isLUB_csSup {s : Set α} (hs : BddAbove s) : IsLUB s (sSup s) := by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · simp only [sSup_empty, isLUB_empty]
  · exact _root_.isLUB_csSup hne hs

/-- In conditionally complete lattices with a bottom element, the nonempty condition can be omitted
from `csSup_le_iff`. -/
@[to_dual OrderTop.le_csInf_iff]
theorem OrderBot.csSup_le_iff {s : Set α} (hs : BddAbove s) {a : α} : sSup s ≤ a ↔ ∀ x ∈ s, x ≤ a :=
  isLUB_le_iff (isLUB_csSup hs)

@[to_dual OrderTop.le_csInf]
theorem OrderBot.csSup_le {s : Set α} {a : α} (h : a ∈ upperBounds s) : sSup s ≤ a :=
  (csSup_le_iff ⟨a, h⟩).2 h

@[to_dual OrderTop.le_csSup]
theorem OrderBot.csInf_le (h : a ∈ s) : sInf s ≤ a := _root_.csInf_le (OrderBot.bddBelow _) h

end

section ConditionallyCompleteLinearOrderBot

@[deprecated (since := "2026-02-26")] alias csInf_univ := sInf_univ

variable [ConditionallyCompleteLinearOrderBot α] {s : Set α} {a : α}

@[deprecated (since := "2026-02-26")] alias csSup_empty := sSup_empty

@[deprecated (since := "2026-03-31")] alias isLUB_csSup' := OrderBot.isLUB_csSup
@[deprecated (since := "2026-03-31")] alias csSup_le_iff' := OrderBot.csSup_le_iff
@[deprecated (since := "2026-03-31")] alias csSup_le' := OrderBot.csSup_le

/-- In conditionally complete orders with a bottom element, the nonempty condition can be omitted
from `lt_csSup_iff`. -/
theorem lt_csSup_iff' (hb : BddAbove s) : a < sSup s ↔ ∃ b ∈ s, a < b := by
  simpa only [not_le, not_forall₂, exists_prop] using (OrderBot.csSup_le_iff hb).not

theorem le_csSup_iff' {s : Set α} {a : α} (h : BddAbove s) :
    a ≤ sSup s ↔ ∀ b, b ∈ upperBounds s → a ≤ b :=
  ⟨fun h _ hb => le_trans h (OrderBot.csSup_le hb), fun hb => hb _ fun _ => le_csSup h⟩

theorem le_csInf_iff'' {s : Set α} {a : α} (ne : s.Nonempty) :
    a ≤ sInf s ↔ ∀ b : α, b ∈ s → a ≤ b :=
  le_csInf_iff (OrderBot.bddBelow _) ne

@[deprecated (since := "2026-03-31")] alias csInf_le' := OrderBot.csInf_le

theorem exists_lt_of_lt_csSup' {s : Set α} {a : α} (h : a < sSup s) : ∃ b ∈ s, a < b := by
  contrapose! h
  exact OrderBot.csSup_le h

theorem notMem_of_lt_csInf' {x : α} {s : Set α} (h : x < sInf s) : x ∉ s :=
  notMem_of_lt_csInf h (OrderBot.bddBelow s)

@[gcongr mid]
theorem csInf_le_csInf' {s t : Set α} (h₁ : t.Nonempty) (h₂ : t ⊆ s) : sInf s ≤ sInf t :=
  csInf_le_csInf (OrderBot.bddBelow s) h₁ h₂

@[gcongr mid]
theorem csSup_le_csSup' {s t : Set α} (h₁ : BddAbove t) (h₂ : s ⊆ t) : sSup s ≤ sSup t := by
  rcases eq_empty_or_nonempty s with rfl | h
  · rw [sSup_empty]
    exact bot_le
  · exact csSup_le_csSup h₁ h h₂

end ConditionallyCompleteLinearOrderBot

instance [ConditionallyCompleteLattice α] [BoundedOrder α] : CompleteLattice α where
  exists_isLUB s := by
    rw [exists_isLUB_iff_isLUB_sSup]
    obtain rfl | hn := s.eq_empty_or_nonempty
    · simp
    · exact isLUB_csSup hn (OrderTop.bddAbove s)
  exists_isGLB s := by
    rw [exists_isGLB_iff_isGLB_sInf]
    obtain rfl | hn := s.eq_empty_or_nonempty
    · simp
    · exact isGLB_csInf hn (OrderBot.bddBelow s)

instance [ConditionallyCompleteLinearOrder α] [BoundedOrder α] : CompleteLinearOrder α where
  __ := ‹ConditionallyCompleteLinearOrder α›
  __ := instCompleteLatticeOfBoundedOrder
  __ := LinearOrder.toBiheytingAlgebra α

namespace WithTop

@[to_dual]
lemma exists_isLUB_cond_of_exists_isLUB_cond [Preorder α]
    (h : ∀ {s : Set α}, s.Nonempty → BddAbove s → ∃ a, IsLUB s a)
    {s : Set (WithTop α)} (hn : s.Nonempty) (hb : BddAbove s) : ∃ a, IsLUB s a := by
  rw [exists_isLUB_iff, ← imp_iff_not_or, or_iff_not_imp_left]
  intro hs hb
  lift s to Set α
  · rintro _ hs' rfl
    exact hs hs'
  rw [preimage_image_eq _ coe_injective] at hb ⊢
  exact h (.of_image hn) hb

@[to_dual]
lemma exists_isGLB_cond_of_exists_isGLB_cond [Preorder α] [Nonempty α]
    (h : ∀ {s : Set α}, s.Nonempty → BddBelow s → ∃ a, IsGLB s a)
    {s : Set (WithTop α)} (hb : BddBelow s) : ∃ a, IsGLB s a := by
  rw [exists_isGLB_iff, or_iff_not_imp_left, ← nonempty_preimage_coe]
  intro hn'
  exact h hn' (bddBelow_preimage_coe.mpr hb)

@[to_dual]
instance [ConditionallyCompleteLattice α] : ConditionallyCompleteLattice (WithTop α) where
  exists_isLUB_cond _ := exists_isLUB_cond_of_exists_isLUB_cond (⟨_, isLUB_csSup · ·⟩)
  exists_isGLB_cond _ _ := exists_isGLB_cond_of_exists_isGLB_cond (⟨_, isGLB_csInf · ·⟩)

instance [ConditionallyCompleteLinearOrder α] : ConditionallyCompleteLinearOrder (WithTop α) where
  __ := instConditionallyCompleteLattice
  __ := linearOrder

@[to_dual existing]
instance _root_.WithBot.instConditionallyCompleteLinearOrder [ConditionallyCompleteLinearOrder α] :
    ConditionallyCompleteLinearOrder (WithBot α) where
  __ := WithBot.instConditionallyCompleteLattice
  __ := WithBot.linearOrder

section

variable [ConditionallyCompleteLinearOrderBot α]

/-- The `sSup` of a non-empty set is its least upper bound for a conditionally
complete lattice with a top. -/
@[deprecated isLUB_csSup (since := "2026-03-31")]
theorem isLUB_sSup' {β : Type*} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : s.Nonempty) : IsLUB s (sSup s) :=
  isLUB_csSup hs

@[deprecated _root_.isLUB_sSup (since := "2026-03-31")]
protected theorem isLUB_sSup (s : Set (WithTop α)) : IsLUB s (sSup s) :=
  _root_.isLUB_sSup s

/-- The `sInf` of a bounded-below set is its greatest lower bound for a conditionally
complete lattice with a top. -/
@[deprecated OrderTop.isGLB_csInf (since := "2026-03-31")]
theorem isGLB_sInf' {β : Type*} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : BddBelow s) : IsGLB s (sInf s) :=
  OrderTop.isGLB_csInf hs

@[deprecated _root_.isGLB_sInf (since := "2026-03-31")]
protected theorem isGLB_sInf (s : Set (WithTop α)) : IsGLB s (sInf s) :=
  _root_.isGLB_sInf s

end

variable [ConditionallyCompleteLattice α]

@[to_dual]
theorem sSup_eq [OrderBot α] {s : Set (WithTop α)} (hs : ⊤ ∉ s)
    (hb : BddAbove ((↑) ⁻¹' s : Set α)) : sSup s = ↑(sSup ((↑) ⁻¹' s) : α) :=
  IsLUB.sSup_eq <| by
    lift s to Set α
    · rintro _ h rfl
      exact hs h
    rw [WithTop.isLUB_image_coe]
    rw [preimage_image_eq _ coe_injective] at hb ⊢
    exact OrderBot.isLUB_csSup hb

@[to_dual]
theorem sSup_ind [OrderBot α] {motive : WithTop α → Prop} {s : Set (WithTop α)}
    (top : ⊤ ∈ s ∨ ¬BddAbove ((↑) ⁻¹' s : Set α) → motive ⊤)
    (coe : ⊤ ∉ s → BddAbove ((↑) ⁻¹' s : Set α) → motive (sSup ((↑) ⁻¹' s) : α)) :
    motive (sSup s) := by
  by_cases h1 : ⊤ ∈ s
  · rw [csSup_eq_top_of_top_mem h1]
    exact top (.inl h1)
  by_cases h2 : BddAbove ((↑) ⁻¹' s : Set α)
  · rw [sSup_eq h1 h2]
    exact coe h1 h2
  · specialize top (.inr h2)
    rw [← isLUB_image_top, image_preimage_eq_of_subset (fun x ↦ by cases x <;> simp [h1])] at h2
    rwa [h2.sSup_eq]

@[to_dual]
theorem sSup_eq_of_nonempty {s : Set (WithTop α)}
    (hs : ⊤ ∉ s) (hn : ((↑) ⁻¹' s : Set α).Nonempty)
    (hb : BddAbove ((↑) ⁻¹' s : Set α)) : sSup s = ↑(sSup ((↑) ⁻¹' s) : α) :=
  IsLUB.sSup_eq <| by
    lift s to Set α
    · rintro _ h rfl
      exact hs h
    rw [WithTop.isLUB_image_coe]
    rw [preimage_image_eq _ coe_injective] at hn hb ⊢
    exact isLUB_csSup hn hb

@[to_dual]
theorem sInf_eq {s : Set (WithTop α)} (hs : ¬s ⊆ {⊤}) (h's : BddBelow s) :
    sInf s = ↑(sInf ((↑) ⁻¹' s) : α) :=
  IsGLB.sInf_eq <| (isGLB_preimage hs).mp <|
    isGLB_csInf (nonempty_preimage_coe.mpr hs) (bddBelow_preimage_coe.mpr h's)

@[to_dual]
theorem coe_sInf' {s : Set α} (hs : s.Nonempty) (h's : BddBelow s) :
    ↑(sInf s) = (sInf ((↑) '' s) : WithTop α) := by
  rw [sInf_eq _ (coe_mono.map_bddBelow h's), preimage_image_eq _ coe_injective]
  rwa [← nonempty_preimage_coe, preimage_image_eq _ coe_injective]

@[to_dual]
theorem coe_sSup' [OrderBot α] {s : Set α} (hs : BddAbove s) :
    ↑(sSup s) = (sSup ((↑) '' s) : WithTop α) := by
  rw [sSup_eq (by simp), preimage_image_eq _ coe_injective]
  rwa [preimage_image_eq _ coe_injective]

@[to_dual]
theorem coe_sSup_of_nonempty' {s : Set α} (hs : BddAbove s) (hn : s.Nonempty) :
    ↑(sSup s) = (sSup ((↑) '' s) : WithTop α) := by
  rw [sSup_eq_of_nonempty (by simp), preimage_image_eq _ coe_injective]
  all_goals rwa [preimage_image_eq _ coe_injective]

/-- A version of `WithTop.coe_sSup'` with a more convenient statement. -/
@[to_dual (attr := norm_cast)]
theorem coe_sSup [OrderBot α] {s : Set α} (hb : BddAbove s) :
    ↑(sSup s) = (⨆ a ∈ s, ↑a : WithTop α) := by
  rw [coe_sSup' hb, sSup_image]

/-- A version of `WithTop.coe_sInf'` with a more convenient statement. -/
@[to_dual (attr := norm_cast)]
theorem coe_sInf [OrderBot α] {s : Set α} (hs : s.Nonempty) (h's : BddBelow s) :
    ↑(sInf s) = (⨅ a ∈ s, ↑a : WithTop α) := by
  rw [coe_sInf' hs h's, sInf_image]

end WithTop

@[deprecated _root_.sInf_empty (since := "2026-03-31")]
theorem WithBot.sInf_empty (α : Type*) [CompleteLattice α] : (sInf ∅ : WithBot α) = ⊤ :=
  _root_.sInf_empty

namespace Monotone

variable [Preorder α] [ConditionallyCompleteLattice β] {f : α → β} (h_mono : Monotone f)
include h_mono

/-! A monotone function into a conditionally complete lattice preserves the ordering properties of
`sSup` and `sInf`. -/


theorem le_csSup_image {s : Set α} {c : α} (hcs : c ∈ s) (h_bdd : BddAbove s) :
    f c ≤ sSup (f '' s) :=
  le_csSup (map_bddAbove h_mono h_bdd) (mem_image_of_mem f hcs)

theorem csSup_image_le {s : Set α} (hs : s.Nonempty) {B : α} (hB : B ∈ upperBounds s) :
    sSup (f '' s) ≤ f B :=
  csSup_le (Nonempty.image f hs) (h_mono.mem_upperBounds_image hB)

-- Porting note: in mathlib3 `f'` is not needed
theorem csInf_image_le {s : Set α} {c : α} (hcs : c ∈ s) (h_bdd : BddBelow s) :
    sInf (f '' s) ≤ f c := by
  let f' : αᵒᵈ → βᵒᵈ := f
  exact le_csSup_image (α := αᵒᵈ) (β := βᵒᵈ)
    (show Monotone f' from fun x y hxy => h_mono hxy) hcs h_bdd

-- Porting note: in mathlib3 `f'` is not needed
theorem le_csInf_image {s : Set α} (hs : s.Nonempty) {B : α} (hB : B ∈ lowerBounds s) :
    f B ≤ sInf (f '' s) := by
  let f' : αᵒᵈ → βᵒᵈ := f
  exact csSup_image_le (α := αᵒᵈ) (β := βᵒᵈ)
    (show Monotone f' from fun x y hxy => h_mono hxy) hs hB

end Monotone

lemma MonotoneOn.csInf_eq_of_subset_of_forall_exists_le
    [Preorder α] [ConditionallyCompleteLattice β] {f : α → β}
    {s t : Set α} (ht : BddBelow (f '' t)) (hf : MonotoneOn f t)
    (hst : s ⊆ t) (h : ∀ y ∈ t, ∃ x ∈ s, x ≤ y) :
    sInf (f '' s) = sInf (f '' t) := by
  obtain rfl | hs := Set.eq_empty_or_nonempty s
  · obtain rfl : t = ∅ := by simpa [Set.eq_empty_iff_forall_notMem] using h
    rfl
  refine le_antisymm ?_ (by gcongr; exacts [ht, hs.image f])
  refine le_csInf ((hs.mono hst).image f) ?_
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro a ha
  obtain ⟨x, hxs, hxa⟩ := h a ha
  exact csInf_le_of_le (ht.mono (image_mono hst)) ⟨x, hxs, rfl⟩ (hf (hst hxs) ha hxa)

lemma MonotoneOn.csSup_eq_of_subset_of_forall_exists_le
    [Preorder α] [ConditionallyCompleteLattice β] {f : α → β}
    {s t : Set α} (ht : BddAbove (f '' t)) (hf : MonotoneOn f t)
    (hst : s ⊆ t) (h : ∀ y ∈ t, ∃ x ∈ s, y ≤ x) :
    sSup (f '' s) = sSup (f '' t) :=
  MonotoneOn.csInf_eq_of_subset_of_forall_exists_le (α := αᵒᵈ) (β := βᵒᵈ) ht hf.dual hst h

theorem MonotoneOn.sInf_image_Icc [Preorder α] [ConditionallyCompleteLattice β]
    {f : α → β} {a b : α} (hab : a ≤ b)
    (h' : MonotoneOn f (Icc a b)) : sInf (f '' Icc a b) = f a := by
  refine IsGLB.csInf_eq ?_ ((nonempty_Icc.mpr hab).image f)
  refine isGLB_iff_le_iff.mpr (fun b' ↦ ⟨?_, ?_⟩)
  · intro hb'
    rintro _ ⟨x, hx, rfl⟩
    exact hb'.trans <| h' (left_mem_Icc.mpr hab) hx hx.1
  · exact fun hb' ↦ hb' ⟨a, by simp [hab]⟩

theorem MonotoneOn.sSup_image_Icc [Preorder α] [ConditionallyCompleteLattice β]
    {f : α → β} {a b : α} (hab : a ≤ b)
    (h' : MonotoneOn f (Icc a b)) : sSup (f '' Icc a b) = f b := by
  have : Icc a b = Icc (α := αᵒᵈ) (toDual b) (toDual a) := by rw [Icc_toDual]; rfl
  rw [this] at h' ⊢
  exact h'.dual_right.dual_left.sInf_image_Icc (β := βᵒᵈ) (α := αᵒᵈ) hab

theorem AntitoneOn.sInf_image_Icc [Preorder α] [ConditionallyCompleteLattice β]
    {f : α → β} {a b : α} (hab : a ≤ b)
    (h' : AntitoneOn f (Icc a b)) : sInf (f '' Icc a b) = f b := by
  have : Icc a b = Icc (α := αᵒᵈ) (toDual b) (toDual a) := by rw [Icc_toDual]; rfl
  rw [this] at h' ⊢
  exact h'.dual_left.sInf_image_Icc (α := αᵒᵈ) hab

theorem AntitoneOn.sSup_image_Icc [Preorder α] [ConditionallyCompleteLattice β]
    {f : α → β} {a b : α} (hab : a ≤ b)
    (h' : AntitoneOn f (Icc a b)) : sSup (f '' Icc a b) = f a :=
  h'.dual_right.sInf_image_Icc hab

/-!
### Supremum/infimum of `Set.image2`

A collection of lemmas showing what happens to the suprema/infima of `s` and `t` when mapped under
a binary function whose partial evaluations are lower/upper adjoints of Galois connections.
-/

section

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β]
  [ConditionallyCompleteLattice γ] {s : Set α} {t : Set β}

variable {l u : α → β → γ} {l₁ u₁ : β → γ → α} {l₂ u₂ : α → γ → β}

theorem csSup_image2_eq_csSup_csSup (h₁ : ∀ b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a) (u₂ a)) (hs₀ : s.Nonempty) (hs₁ : BddAbove s)
    (ht₀ : t.Nonempty) (ht₁ : BddAbove t) : sSup (image2 l s t) = l (sSup s) (sSup t) :=
  isLUB_image2_of_isLUB_isLUB h₁ h₂ (isLUB_csSup hs₀ hs₁) (isLUB_csSup ht₀ ht₁)
    |>.csSup_eq (hs₀.image2 ht₀)

theorem csSup_image2_eq_csSup_csInf (h₁ : ∀ b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddBelow t → sSup (image2 l s t) = l (sSup s) (sInf t) :=
  csSup_image2_eq_csSup_csSup (β := βᵒᵈ) h₁ h₂

theorem csSup_image2_eq_csInf_csSup (h₁ : ∀ b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a) (u₂ a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddAbove t → sSup (image2 l s t) = l (sInf s) (sSup t) :=
  csSup_image2_eq_csSup_csSup (α := αᵒᵈ) h₁ h₂

theorem csSup_image2_eq_csInf_csInf (h₁ : ∀ b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddBelow t → sSup (image2 l s t) = l (sInf s) (sInf t) :=
  csSup_image2_eq_csSup_csSup (α := αᵒᵈ) (β := βᵒᵈ) h₁ h₂

theorem csInf_image2_eq_csInf_csInf (h₁ : ∀ b, GaloisConnection (l₁ b) (swap u b))
    (h₂ : ∀ a, GaloisConnection (l₂ a) (u a)) (hs₀ : s.Nonempty) (hs₁ : BddBelow s)
    (ht₀ : t.Nonempty) (ht₁ : BddBelow t) : sInf (image2 u s t) = u (sInf s) (sInf t) :=
  isGLB_image2_of_isGLB_isGLB h₁ h₂ (isGLB_csInf hs₀ hs₁) (isGLB_csInf ht₀ ht₁)
    |>.csInf_eq (hs₀.image2 ht₀)

theorem csInf_image2_eq_csInf_csSup (h₁ : ∀ b, GaloisConnection (l₁ b) (swap u b))
    (h₂ : ∀ a, GaloisConnection (toDual ∘ l₂ a) (u a ∘ ofDual)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddAbove t → sInf (image2 u s t) = u (sInf s) (sSup t) :=
  csInf_image2_eq_csInf_csInf (β := βᵒᵈ) h₁ h₂

theorem csInf_image2_eq_csSup_csInf (h₁ : ∀ b, GaloisConnection (toDual ∘ l₁ b) (swap u b ∘ ofDual))
    (h₂ : ∀ a, GaloisConnection (l₂ a) (u a)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddBelow t → sInf (image2 u s t) = u (sSup s) (sInf t) :=
  csInf_image2_eq_csInf_csInf (α := αᵒᵈ) h₁ h₂

theorem csInf_image2_eq_csSup_csSup (h₁ : ∀ b, GaloisConnection (toDual ∘ l₁ b) (swap u b ∘ ofDual))
    (h₂ : ∀ a, GaloisConnection (toDual ∘ l₂ a) (u a ∘ ofDual)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddAbove t → sInf (image2 u s t) = u (sSup s) (sSup t) :=
  csInf_image2_eq_csInf_csInf (α := αᵒᵈ) (β := βᵒᵈ) h₁ h₂

end
