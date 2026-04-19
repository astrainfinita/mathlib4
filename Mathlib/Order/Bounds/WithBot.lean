/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Order.Bounds.Image
public import Mathlib.Order.WithBot

/-!
-/

@[expose] public section

variable {α : Type*} [Preorder α]

namespace WithTop

@[to_dual]
theorem isLUB_image_top {s : Set α} :
    IsLUB ((↑) '' s) (⊤ : WithTop α) ↔ ¬BddAbove s := by
  refine ⟨fun h ⟨_, hb⟩ ↦ ?_, fun hb ↦ ⟨fun _ _ ↦ le_top, fun a ha ↦ ?_⟩⟩
  · simpa using h.2 (coe_mono.mem_upperBounds_image hb)
  · cases a with | top => rfl | coe a => ?_
    simp only [mem_upperBounds_image, coe_le_coe] at ha
    exact absurd ⟨a, ha⟩ hb

@[to_dual]
theorem isLUB_image_coe {s : Set α} {a : α} :
    IsLUB ((↑) '' s) (a : WithTop α) ↔ IsLUB s a := by
  rw [isLUB_image_iff coe_le_coe, and_iff_left_iff_imp]
  intro h b hb
  cases b with
  | top => exact ⟨a, ⟨a, h.1, rfl⟩, le_top⟩
  | coe b => exact ⟨b, by simpa [mem_upperBounds] using hb⟩

@[to_dual]
theorem exists_isLUB_iff {s : Set (WithTop α)} :
    (∃ a, IsLUB s a) ↔
      ⊤ ∈ s ∨ ¬BddAbove ((↑) ⁻¹' s : Set α) ∨ ∃ a, IsLUB ((↑) ⁻¹' s : Set α) a := by
  by_cases hs : ⊤ ∈ s
  · simpa [hs] using ⟨⊤, (isGreatest_top_iff.mpr hs).isLUB⟩
  lift s to Set α
  · rintro _ hs' rfl
    exact hs hs'
  simp only [hs, Set.preimage_image_eq _ coe_injective, false_or]
  simp only [WithTop.exists, isLUB_image_top, isLUB_image_coe]

@[to_dual]
theorem isGLB_top {s : Set (WithTop α)} :
    IsGLB s (⊤ : WithTop α) ↔ s ⊆ {⊤} := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [Set.eq_empty_iff_forall_notMem, mem_lowerBounds] using h.1
  · obtain rfl | rfl := Set.subset_singleton_iff_eq.mp h <;> simp

@[to_dual]
theorem isGLB_image_top {s : Set α} :
    IsGLB ((↑) '' s) (⊤ : WithTop α) ↔ s = ∅ := by
  simp [isGLB_top, Set.eq_empty_iff_forall_notMem]

@[to_dual]
theorem isGLB_image_coe {s : Set α} {a : α} :
    IsGLB ((↑) '' s) (a : WithTop α) ↔ s.Nonempty ∧ IsGLB s a := by
  refine ⟨fun h ↦ ⟨?_, h.of_image coe_le_coe⟩,
    fun ⟨hs, h⟩ ↦ ⟨coe_mono.mem_lowerBounds_image h.1, fun b hb ↦ ?_⟩⟩
  · contrapose h
    rw [Set.not_nonempty_iff_eq_empty] at h
    subst h
    simpa using fun h ↦ not_top_le_coe _ (h _)
  cases b with
  | top => exact hs.elim (by simpa [mem_lowerBounds] using hb)
  | coe b =>
    simp only [mem_lowerBounds, Set.forall_mem_image, coe_le_coe] at hb ⊢
    exact h.2 hb

omit [Preorder α] in
@[to_dual]
theorem nonempty_preimage_coe {s : Set (WithTop α)} :
    ((↑) ⁻¹' s : Set α).Nonempty ↔ ¬s ⊆ {⊤} := by
  rw [← Set.diff_nonempty, ← Set.image_nonempty (f := ((↑) : α → WithTop α)),
    Set.image_preimage_eq_inter_range]
  congr! 1
  ext; simp [ne_top_iff_exists]

@[to_dual]
theorem lowerBounds_image_coe {s : Set α} (hs : s.Nonempty) :
    lowerBounds ((↑) '' s : Set (WithTop α)) = (↑) '' lowerBounds s := by
  ext a
  rw [mem_lowerBounds_image]
  cases a with | top => simpa [mem_lowerBounds] | coe => simp [mem_lowerBounds]

@[to_dual]
theorem lowerBounds_preimage_coe (s : Set (WithTop α)) :
    lowerBounds ((↑) ⁻¹' s : Set α) = (↑) ⁻¹' lowerBounds s := by
  ext a; simp [mem_lowerBounds, WithTop.forall]

@[to_dual]
theorem lowerBounds_image_preimage_coe (s : Set (WithTop α)) :
    lowerBounds ((↑) '' ((↑) ⁻¹' s : Set α)) = lowerBounds s := by
  refine subset_antisymm ?_ (lowerBounds_mono_set (Set.image_preimage_subset _ _))
  intro b hb c hc
  cases c with | top => exact le_top | coe => exact hb (Set.mem_image_of_mem _ hc)

@[to_dual]
theorem isGLB_preimage {s : Set (WithTop α)} {a : α} (hs : ¬s ⊆ {⊤}) :
    IsGLB ((↑) ⁻¹' s) a ↔ IsGLB s (a : WithTop α) := by
  rw [← nonempty_preimage_coe] at hs
  simp [← isGLB_congr (lowerBounds_image_preimage_coe s), isGLB_image_coe, hs]

@[to_dual]
theorem exists_isGLB_iff {s : Set (WithTop α)} :
    (∃ a, IsGLB s a) ↔ s ⊆ {⊤} ∨ ∃ a, IsGLB ((↑) ⁻¹' s : Set α) a := by
  by_cases hs : s ⊆ {⊤}
  · obtain rfl | rfl := Set.subset_singleton_iff_eq.mp hs
    · simpa [hs] using ⟨⊤, isTop_top⟩
    · simpa using ⟨⊤, isGLB_singleton⟩
  simp only [hs, isGLB_preimage hs, WithTop.exists, isGLB_top]

@[to_dual]
theorem bddBelow_preimage_coe [Nonempty α] {s : Set (WithTop α)} :
    BddBelow ((↑) ⁻¹' s : Set α) ↔ BddBelow s := by
  obtain rfl | hn := Set.eq_empty_or_nonempty s
  · simp
  rw [BddBelow, BddBelow, lowerBounds_preimage_coe, nonempty_preimage_coe, Set.not_subset]
  refine ⟨fun ⟨_, h, _⟩ ↦ ⟨_, h⟩, fun ⟨a, ha⟩ ↦ ?_⟩
  cases a with
  | top => exact ⟨Classical.arbitrary α, lowerBounds_mono_mem le_top ha, coe_ne_top⟩
  | coe a => exact ⟨a, ha, coe_ne_top⟩

@[to_dual (attr := simp)]
theorem sInf_empty : sInf (∅ : Set (WithTop α)) = ⊤ :=
  WithTop.top_le_iff.mp (isGLB_empty_iff.mp isGLB_empty.isGLB_sInf _)

end WithTop
