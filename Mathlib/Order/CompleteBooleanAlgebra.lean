/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Logic.Pairwise
public import Mathlib.Order.CompleteLattice.Lemmas
public import Mathlib.Order.Directed
public import Mathlib.Order.GaloisConnection.Basic

/-!
# Frames, completely distributive lattices and complete Boolean algebras

In this file we define and provide API for (co)frames, completely distributive lattices and
complete Boolean algebras.

We distinguish two different distributivity properties:
1. `inf_iSup_eq : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i` (finite `⊓` distributes over infinite `⨆`).
  This is required by `Frame`, `CompleteDistribLattice`, and `CompleteBooleanAlgebra`
  (`Coframe`, etc., require the dual property).
2. `iInf_iSup_eq : (⨅ i, ⨆ j, f i j) = ⨆ s, ⨅ i, f i (s i)`
  (infinite `⨅` distributes over infinite `⨆`).
  This stronger property is called "completely distributive",
  and is required by `CompletelyDistribLattice` and `CompleteAtomicBooleanAlgebra`.

## Typeclasses

* `Order.Frame`: Frame: A complete lattice whose `⊓` distributes over `⨆`.
* `Order.Coframe`: Coframe: A complete lattice whose `⊔` distributes over `⨅`.
* `CompleteDistribLattice`: Complete distributive lattices: A complete lattice whose `⊓` and `⊔`
  distribute over `⨆` and `⨅` respectively.
* `CompletelyDistribLattice`: Completely distributive lattices: A complete lattice whose
  `⨅` and `⨆` satisfy `iInf_iSup_eq`.
* `CompleteBooleanAlgebra`: Complete Boolean algebra: A Boolean algebra whose `⊓`
  and `⊔` distribute over `⨆` and `⨅` respectively.
* `CompleteAtomicBooleanAlgebra`: Complete atomic Boolean algebra:
  A complete Boolean algebra which is additionally completely distributive.
  (This implies that it's (co)atom(ist)ic.)

A set of opens gives rise to a topological space precisely if it forms a frame. Such a frame is also
completely distributive, but not all frames are. `Filter` is a coframe but not a completely
distributive lattice.

## References

* [Wikipedia, *Complete Heyting algebra*](https://en.wikipedia.org/wiki/Complete_Heyting_algebra)
* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]
-/

@[expose] public section

open Function Set

universe u v w w'

variable {α : Type u} {β : Type v} {ι : Sort w} {κ : ι → Sort w'}

/-- Structure containing the minimal axioms required to check that an order is a frame. Do NOT use,
except for implementing `Order.Frame` via `Order.Frame.ofMinimalAxioms`.

This structure omits the `himp`, `compl` fields, which can be recovered using
`Order.Frame.ofMinimalAxioms`. -/
@[deprecated "Use `Order.Frame` instead" (since := "2026-04-24")]
structure Order.Frame.MinimalAxioms (α : Type u) extends Lattice α, CompleteLattice α where
  inf_sSup_le_iSup_inf (a : α) (s : Set α) : a ⊓ sSup s ≤ ⨆ b ∈ s, a ⊓ b

/-- Structure containing the minimal axioms required to check that an order is a coframe. Do NOT
use, except for implementing `Order.Coframe` via `Order.Coframe.ofMinimalAxioms`.

This structure omits the `sdiff`, `hnot` fields, which can be recovered using
`Order.Coframe.ofMinimalAxioms`. -/
@[deprecated "Use `Order.Coframe` instead" (since := "2026-04-24")]
structure Order.Coframe.MinimalAxioms (α : Type u) extends Lattice α, CompleteLattice α where
  iInf_sup_le_sup_sInf (a : α) (s : Set α) : ⨅ b ∈ s, a ⊔ b ≤ a ⊔ sInf s

/-- A frame, aka complete Heyting algebra, is a complete lattice whose `⊓` distributes over `⨆`. -/
class Order.Frame (α : Type*) [Lattice α] extends CompleteLattice α where
  /-- `⊓` distributes over `⨆`. -/
  inf_sSup_le_iSup_inf (a : α) (s : Set α) : a ⊓ sSup s ≤ ⨆ b ∈ s, a ⊓ b

/-- `⊓` distributes over `⨆`. -/
theorem inf_sSup_eq {α : Type*} [Lattice α] [Order.Frame α] {s : Set α} {a : α} :
    a ⊓ sSup s = ⨆ b ∈ s, a ⊓ b :=
  (Order.Frame.inf_sSup_le_iSup_inf _ _).antisymm iSup_inf_le_inf_sSup

/-- A coframe, aka complete Brouwer algebra or complete co-Heyting algebra, is a complete lattice
whose `⊔` distributes over `⨅`. -/
@[to_dual]
class Order.Coframe (α : Type*) [Lattice α] extends CompleteLattice α where
  /-- `⊔` distributes over `⨅`. -/
  iInf_sup_le_sup_sInf (a : α) (s : Set α) : ⨅ b ∈ s, a ⊔ b ≤ a ⊔ sInf s

/-- `⊔` distributes over `⨅`. -/
theorem sup_sInf_eq {α : Type*} [Lattice α] [Order.Coframe α] {s : Set α} {a : α} :
    a ⊔ sInf s = ⨅ b ∈ s, a ⊔ b :=
  sup_sInf_le_iInf_sup.antisymm (Order.Coframe.iInf_sup_le_sup_sInf _ _)

open Order

set_option linter.deprecated false in
/-- Structure containing the minimal axioms required to check that an order is a complete
distributive lattice. Do NOT use, except for implementing `CompleteDistribLattice` via
`CompleteDistribLattice.ofMinimalAxioms`.

This structure omits the `himp`, `compl`, `sdiff`, `hnot` fields, which can be recovered using
`CompleteDistribLattice.ofMinimalAxioms`. -/
@[deprecated "Use `CompleteDistribLattice` instead" (since := "2026-04-24")]
structure CompleteDistribLattice.MinimalAxioms (α : Type u)
    extends Lattice α, CompleteLattice α,
      toFrameMinimalAxioms : Frame.MinimalAxioms α,
      toCoframeMinimalAxioms : Coframe.MinimalAxioms α where

-- We give those projections better name further down
attribute [nolint docBlame] CompleteDistribLattice.MinimalAxioms.toFrameMinimalAxioms
  CompleteDistribLattice.MinimalAxioms.toCoframeMinimalAxioms

/-- A complete distributive lattice is a complete lattice whose `⊔` and `⊓` respectively
distribute over `⨅` and `⨆`. -/
class CompleteDistribLattice (α : Type*) [Lattice α] extends Frame α, Coframe α

/-- Structure containing the minimal axioms required to check that an order is a completely
distributive. Do NOT use, except for implementing `CompletelyDistribLattice` via
`CompletelyDistribLattice.ofMinimalAxioms`.

This structure omits the `himp`, `compl`, `sdiff`, `hnot` fields, which can be recovered using
`CompletelyDistribLattice.ofMinimalAxioms`. -/
@[deprecated "Use `CompletelyDistribLattice` instead" (since := "2026-04-24")]
structure CompletelyDistribLattice.MinimalAxioms (α : Type u) extends Lattice α,
    CompleteLattice α where
  protected iInf_iSup_eq {ι : Type u} {κ : ι → Type u} (f : ∀ a, κ a → α) :
    (⨅ a, ⨆ b, f a b) = ⨆ g : ∀ a, κ a, ⨅ a, f a (g a)

/-- A completely distributive lattice is a complete lattice whose `⨅` and `⨆`
distribute over each other. -/
class CompletelyDistribLattice (α : Type u) [Lattice α] extends CompleteLattice α where
  protected iInf_iSup_eq {ι : Type u} {κ : ι → Type u} (f : ∀ a, κ a → α) :
    (⨅ a, ⨆ b, f a b) = ⨆ g : ∀ a, κ a, ⨅ a, f a (g a)

theorem le_iInf_iSup [Lattice α] [CompleteLattice α] {f : ∀ a, κ a → α} :
    (⨆ g : ∀ a, κ a, ⨅ a, f a (g a)) ≤ ⨅ a, ⨆ b, f a b :=
  iSup_le fun _ => le_iInf fun a => le_trans (iInf_le _ a) (le_iSup _ _)

lemma iSup_iInf_le [Lattice α] [CompleteLattice α] {f : ∀ a, κ a → α} :
    ⨆ a, ⨅ b, f a b ≤ ⨅ g : ∀ a, κ a, ⨆ a, f a (g a) :=
  le_iInf_iSup (α := αᵒᵈ)

section Order.Frame
variable [Lattice α] [Frame α] {s : Set α} {a b : α}

lemma sSup_inf_eq : sSup s ⊓ b = ⨆ a ∈ s, a ⊓ b := by
  simpa only [inf_comm] using @inf_sSup_eq α _ _ s b

lemma iSup_inf_eq (f : ι → α) (a : α) : (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a := by
  rw [iSup, sSup_inf_eq, iSup_range]

lemma inf_iSup_eq (a : α) (f : ι → α) : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i := by
  simpa only [inf_comm] using iSup_inf_eq f a

lemma inf_iSup₂_eq {f : ∀ i, κ i → α} (a : α) : (a ⊓ ⨆ i, ⨆ j, f i j) = ⨆ i, ⨆ j, a ⊓ f i j := by
  simp only [inf_iSup_eq]

/-- Construct a `HeytingAlgebra` instance from a frame.

This sets `a ⇨ b := sSup {c | c ⊓ a ≤ b}` and `aᶜ := a ⇨ ⊥`. -/
@[instance_reducible]
def HeytingAlgebra.ofFrame [Lattice α] [BoundedOrder α] [Frame α] : HeytingAlgebra α where
  compl a := sSup {c | c ⊓ a ≤ ⊥}
  himp a b := sSup {c | c ⊓ a ≤ b}
  le_himp_iff _ b c :=
    ⟨fun h ↦ (inf_le_inf_right _ h).trans (by simp [sSup_inf_eq]), fun h ↦ le_sSup h⟩
  himp_bot _ := rfl

end Order.Frame

namespace Order.Frame

/-- A `CompleteLattice` which is a `HeytingAlgebra` is automatically a `Frame`. -/
instance (priority := 100) ofHeytingAlgebra [HeytingAlgebra α] [CompleteLattice α] : Frame α where
  inf_sSup_le_iSup_inf _ _ := gc_inf_himp.l_sSup.le

set_option linter.deprecated false

/-- Construct a frame instance using the minimal amount of work needed.

This sets `a ⇨ b := sSup {c | c ⊓ a ≤ b}` and `aᶜ := a ⇨ ⊥`. -/
-- See note [reducible non-instances]
@[deprecated "`Order.Frame.MinimalAxioms` has been deprecated" (since := "2026-04-24")]
abbrev ofMinimalAxioms (minAx : MinimalAxioms α) :
    letI := minAx.toLattice
    Frame α where
  __ := minAx.toLattice
  __ := minAx

namespace MinimalAxioms
variable (minAx : MinimalAxioms α) {s : Set α} {a b : α}

@[deprecated "`Order.Frame.MinimalAxioms` has been deprecated" (since := "2026-04-24")]
lemma inf_sSup_eq :
    letI := minAx.toLattice; letI := ofMinimalAxioms minAx
    a ⊓ sSup s = ⨆ b ∈ s, a ⊓ b :=
  letI := minAx.toLattice; letI := ofMinimalAxioms minAx
  _root_.inf_sSup_eq

@[deprecated "`Order.Frame.MinimalAxioms` has been deprecated" (since := "2026-04-24")]
lemma sSup_inf_eq :
    letI := minAx.toLattice; letI := ofMinimalAxioms minAx
    sSup s ⊓ b = ⨆ a ∈ s, a ⊓ b := by
  simpa only [inf_comm] using @inf_sSup_eq α _ s b

@[deprecated "`Order.Frame.MinimalAxioms` has been deprecated" (since := "2026-04-24")]
lemma iSup_inf_eq (f : ι → α) (a : α) :
    letI := minAx.toLattice; letI := ofMinimalAxioms minAx
    (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a :=
  letI := minAx.toLattice; letI := ofMinimalAxioms minAx
  _root_.iSup_inf_eq f a

@[deprecated "`Order.Frame.MinimalAxioms` has been deprecated" (since := "2026-04-24")]
lemma inf_iSup_eq (a : α) (f : ι → α) :
    letI := minAx.toLattice; letI := ofMinimalAxioms minAx
    (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i := by
  simpa only [inf_comm] using minAx.iSup_inf_eq f a

@[deprecated "`Order.Frame.MinimalAxioms` has been deprecated" (since := "2026-04-24")]
lemma inf_iSup₂_eq {f : ∀ i, κ i → α} (a : α) :
    letI := minAx.toLattice; letI := ofMinimalAxioms minAx
    (a ⊓ ⨆ i, ⨆ j, f i j) = ⨆ i, ⨆ j, a ⊓ f i j := by
  simp only [inf_iSup_eq]

/-- The `Order.Frame.MinimalAxioms` element corresponding to a frame. -/
@[deprecated "`Order.Frame.MinimalAxioms` has been deprecated" (since := "2026-04-24"),
  implicit_reducible]
def of [Lattice α] [Frame α] : MinimalAxioms α where
  __ := ‹Frame α›
  inf_sSup_le_iSup_inf a s := _root_.inf_sSup_eq.le

end Order.Frame.MinimalAxioms

section Order.Coframe.MinimalAxioms
variable [Lattice α] [Coframe α] {s : Set α} {a b : α}

lemma sInf_sup_eq : sInf s ⊔ b = ⨅ a ∈ s, a ⊔ b := by
  simpa only [sup_comm] using @sup_sInf_eq α _ _ s b

lemma iInf_sup_eq (f : ι → α) (a : α) : (⨅ i, f i) ⊔ a = ⨅ i, f i ⊔ a := by
  rw [iInf, sInf_sup_eq, iInf_range]

lemma sup_iInf_eq (a : α) (f : ι → α) : (a ⊔ ⨅ i, f i) = ⨅ i, a ⊔ f i := by
  simpa only [sup_comm] using iInf_sup_eq f a

lemma sup_iInf₂_eq {f : ∀ i, κ i → α} (a : α) : (a ⊔ ⨅ i, ⨅ j, f i j) = ⨅ i, ⨅ j, a ⊔ f i j := by
  simp only [sup_iInf_eq]

end MinimalAxioms

/-- Construct a `CoheytingAlgebra` instance from a coframe.

This sets `a \ b := sInf {c | a ≤ b ⊔ c}` and `￢a := ⊤ \ a`. -/
@[instance_reducible]
def CoheytingAlgebra.ofCoframe [Lattice α] [BoundedOrder α] [Coframe α] : CoheytingAlgebra α where
  hnot a := sInf {c | ⊤ ≤ a ⊔ c}
  sdiff a b := sInf {c | a ≤ b ⊔ c}
  sdiff_le_iff a b _ :=
    ⟨fun h ↦ (sup_le_sup_left h _).trans' (by simp [sup_sInf_eq]), fun h ↦ sInf_le h⟩
  top_sdiff _ := rfl

namespace Order.Coframe

/-- A `CompleteLattice` which is a `CoheytingAlgebra` is automatically a `Coframe`. -/
instance (priority := 100) ofCoheytingAlgebra [CoheytingAlgebra α] [CompleteLattice α] :
    Coframe α where
  iInf_sup_le_sup_sInf _ _ := gc_sdiff_sup.u_sInf.ge

set_option linter.deprecated false

/-- Construct a coframe instance using the minimal amount of work needed.

This sets `a \ b := sInf {c | a ≤ b ⊔ c}` and `￢a := ⊤ \ a`. -/
-- See note [reducible non-instances]
@[deprecated "`Order.Coframe.MinimalAxioms` has been deprecated" (since := "2026-04-24")]
abbrev ofMinimalAxioms (minAx : MinimalAxioms α) :
    letI := minAx.toLattice
    Coframe α where
  __ := minAx.toLattice
  __ := minAx

namespace MinimalAxioms
variable (minAx : MinimalAxioms α) {s : Set α} {a b : α}

@[deprecated "`Order.Coframe.MinimalAxioms` has been deprecated" (since := "2026-04-24")]
lemma sup_sInf_eq :
    letI := minAx.toLattice; letI := ofMinimalAxioms minAx
    a ⊔ sInf s = ⨅ b ∈ s, a ⊔ b :=
  letI := minAx.toLattice; letI := ofMinimalAxioms minAx
  _root_.sup_sInf_eq

@[deprecated "`Order.Coframe.MinimalAxioms` has been deprecated" (since := "2026-04-24")]
lemma sInf_sup_eq :
    letI := minAx.toLattice; letI := ofMinimalAxioms minAx
    sInf s ⊔ b = ⨅ a ∈ s, a ⊔ b := by
  simpa only [sup_comm] using @sup_sInf_eq α _ s b

@[deprecated "`Order.Coframe.MinimalAxioms` has been deprecated" (since := "2026-04-24")]
lemma iInf_sup_eq (f : ι → α) (a : α) :
    letI := minAx.toLattice; letI := ofMinimalAxioms minAx
    (⨅ i, f i) ⊔ a = ⨅ i, f i ⊔ a :=
    letI := minAx.toLattice; letI := ofMinimalAxioms minAx
  _root_.iInf_sup_eq f a

@[deprecated "`Order.Coframe.MinimalAxioms` has been deprecated" (since := "2026-04-24")]
lemma sup_iInf_eq (a : α) (f : ι → α) :
    letI := minAx.toLattice; letI := ofMinimalAxioms minAx
    (a ⊔ ⨅ i, f i) = ⨅ i, a ⊔ f i := by
  simpa only [sup_comm] using minAx.iInf_sup_eq f a

@[deprecated "`Order.Coframe.MinimalAxioms` has been deprecated" (since := "2026-04-24")]
lemma sup_iInf₂_eq {f : ∀ i, κ i → α} (a : α) :
    letI := minAx.toLattice; letI := ofMinimalAxioms minAx
    (a ⊔ ⨅ i, ⨅ j, f i j) = ⨅ i, ⨅ j, a ⊔ f i j := by
  simp only [sup_iInf_eq]

/-- The `Order.Coframe.MinimalAxioms` element corresponding to a frame. -/
@[deprecated "`Order.Coframe.MinimalAxioms` has been deprecated" (since := "2026-04-24"),
  implicit_reducible]
def of [Lattice α] [Coframe α] : MinimalAxioms α where
  __ := ‹Coframe α›
  iInf_sup_le_sup_sInf a s := _root_.sup_sInf_eq.ge

end Order.Coframe.MinimalAxioms

namespace CompleteDistribLattice.MinimalAxioms
set_option linter.deprecated false
variable (minAx : MinimalAxioms α)

/-- The `CompleteDistribLattice.MinimalAxioms` element corresponding to a complete distrib lattice.
-/
@[deprecated "`CompleteDistribLattice.MinimalAxioms` has been deprecated" (since := "2026-04-24"),
  implicit_reducible]
def of [Lattice α] [CompleteDistribLattice α] : MinimalAxioms α where
  __ := ‹CompleteDistribLattice α›
  inf_sSup_le_iSup_inf a s := inf_sSup_eq.le
  iInf_sup_le_sup_sInf a s := sup_sInf_eq.ge

/-- Turn minimal axioms for `CompleteDistribLattice` into minimal axioms for `Order.Frame`. -/
@[deprecated "`CompleteDistribLattice.MinimalAxioms` has been deprecated" (since := "2026-04-24")]
abbrev toFrame : Frame.MinimalAxioms α := minAx.toFrameMinimalAxioms

/-- Turn minimal axioms for `CompleteDistribLattice` into minimal axioms for `Order.Coframe`. -/
@[deprecated "`CompleteDistribLattice.MinimalAxioms` has been deprecated" (since := "2026-04-24")]
abbrev toCoframe : Coframe.MinimalAxioms α where __ := minAx

end MinimalAxioms

/-- A `CompleteLattice` which is a `BiheytingAlgebra` is automatically a `CompleteDistribLattice`.
-/
instance (priority := 100) ofBiheytingAlgebra [BiheytingAlgebra α] [CompleteLattice α] :
    CompleteDistribLattice α where
  inf_sSup_le_iSup_inf _ _ := gc_inf_himp.l_sSup.le
  iInf_sup_le_sup_sInf _ _ := gc_sdiff_sup.u_sInf.ge

set_option linter.deprecated false

/-- Construct a complete distrib lattice instance using the minimal amount of work needed.

This sets `a ⇨ b := sSup {c | c ⊓ a ≤ b}`, `aᶜ := a ⇨ ⊥`, `a \ b := sInf {c | a ≤ b ⊔ c}` and
`￢a := ⊤ \ a`. -/
-- See note [reducible non-instances]
@[deprecated "`CompleteDistribLattice.MinimalAxioms` has been deprecated" (since := "2026-04-24")]
abbrev ofMinimalAxioms (minAx : MinimalAxioms α) :
    letI := minAx.toLattice
    CompleteDistribLattice α where
  __ := minAx.toLattice
  __ := Frame.ofMinimalAxioms minAx.toFrame
  __ := Coframe.ofMinimalAxioms minAx.toCoframe

end CompleteDistribLattice

/-- Construct a `BiheytingAlgebra` instance from a coframe.

This sets `a \ b := sInf {c | a ≤ b ⊔ c}` and `￢a := ⊤ \ a`. -/
@[instance_reducible]
def CoheytingAlgebra.ofCompleteDistribLattice
    [Lattice α] [BoundedOrder α] [CompleteDistribLattice α] : BiheytingAlgebra α where
  __ := HeytingAlgebra.ofFrame
  __ := CoheytingAlgebra.ofCoframe

section CompletelyDistribLattice
variable [Lattice α] [CompletelyDistribLattice α]

lemma iInf_iSup_eq (f : ∀ a, κ a → α) : ⨅ i, ⨆ j, f i j = ⨆ g : ∀ i, κ i, ⨅ i, f i (g i) := by
  refine le_antisymm ?_ le_iInf_iSup
  calc
    _ = ⨅ a : range (range <| f ·), ⨆ b : a.1, b.1 := by
      simp_rw [iInf_subtype, iInf_range, iSup_subtype, iSup_range]
    _ = _ := CompletelyDistribLattice.iInf_iSup_eq _
    _ ≤ _ := iSup_le fun g => by
      refine le_trans ?_ <| le_iSup _ fun a => Classical.choose (g ⟨_, a, rfl⟩).2
      refine le_iInf fun a => le_trans (iInf_le _ ⟨range (f a), a, rfl⟩) ?_
      rw [← Classical.choose_spec (g ⟨_, a, rfl⟩).2]

lemma iSup_iInf_eq (f : ∀ i, κ i → α) : ⨆ i, ⨅ j, f i j = ⨅ g : ∀ i, κ i, ⨆ i, f i (g i) := by
  refine le_antisymm iSup_iInf_le ?_
  rw [iInf_iSup_eq]
  refine iSup_le fun g => ?_
  have ⟨a, ha⟩ : ∃ a, ∀ b, ∃ f, ∃ h : a = g f, h ▸ b = f (g f) := by
    by_contra! h
    choose h hh using h
    have := hh _ h rfl
    contradiction
  refine le_trans ?_ (le_iSup _ a)
  refine le_iInf fun b => ?_
  obtain ⟨h, rfl, rfl⟩ := ha b
  exact iInf_le _ _

end CompletelyDistribLattice

instance (priority := 100) CompletelyDistribLattice.toCompleteDistribLattice [Lattice α]
    [CompletelyDistribLattice α] : CompleteDistribLattice α where
  inf_sSup_le_iSup_inf a s := by
    calc
      _ = ⨅ i : ULift.{u} Bool, ⨆ j : match i with | .up true => PUnit.{u + 1} | .up false => s,
          match i with
          | .up true => a
          | .up false => j := by simp [sSup_eq_iSup', iSup_unique, iInf_bool_eq]
      _ ≤ _ := by
        simp only [iInf_iSup_eq, iInf_ulift, iInf_bool_eq, iSup_le_iff]
        exact fun x ↦ le_biSup _ (x (.up false)).2
  iInf_sup_le_sup_sInf a s := by
    calc
      _ ≤ ⨆ i : ULift.{u} Bool, ⨅ j : match i with | .up true => PUnit.{u + 1} | .up false => s,
          match i with
          | .up true => a
          | .up false => j := by
        simp only [iSup_iInf_eq, iSup_ulift, iSup_bool_eq, le_iInf_iff]
        exact fun x ↦ biInf_le _ (x (.up false)).2
      _ = _ := by simp [sInf_eq_iInf', iInf_unique, iSup_bool_eq]

namespace CompletelyDistribLattice

set_option linter.deprecated false

/-- Construct a completely distributive lattice instance using the minimal amount of work needed.

This sets `a ⇨ b := sSup {c | c ⊓ a ≤ b}`, `aᶜ := a ⇨ ⊥`, `a \ b := sInf {c | a ≤ b ⊔ c}` and
`￢a := ⊤ \ a`. -/
-- See note [reducible non-instances]
@[deprecated "`CompleteDistribLattice.MinimalAxioms` has been deprecated" (since := "2026-04-24")]
abbrev ofMinimalAxioms (minAx : MinimalAxioms α) :
    let := minAx.toLattice
    CompletelyDistribLattice α where
  __ := minAx.toLattice
  __ := minAx

namespace MinimalAxioms
variable (minAx : MinimalAxioms α)

/-- Turn minimal axioms for `CompletelyDistribLattice` into minimal axioms for
`CompleteDistribLattice`. -/
@[deprecated "`CompleteDistribLattice.MinimalAxioms` has been deprecated" (since := "2026-04-24")]
abbrev toCompleteDistribLattice : CompleteDistribLattice.MinimalAxioms α where
  __ := minAx
  inf_sSup_le_iSup_inf _ _ :=
    let := minAx.toLattice; let := ofMinimalAxioms minAx
    inf_sSup_eq.le
  iInf_sup_le_sup_sInf _ _ :=
    let := minAx.toLattice; let := ofMinimalAxioms minAx
    sup_sInf_eq.ge

@[deprecated "`CompleteDistribLattice.MinimalAxioms` has been deprecated" (since := "2026-04-24")]
lemma iInf_iSup_eq' (f : ∀ a, κ a → α) :
    let _ := minAx.toLattice; let := ofMinimalAxioms minAx
    ⨅ i, ⨆ j, f i j = ⨆ g : ∀ i, κ i, ⨅ i, f i (g i) :=
  let _ := minAx.toLattice; let := ofMinimalAxioms minAx
  iInf_iSup_eq f

@[deprecated "`CompleteDistribLattice.MinimalAxioms` has been deprecated" (since := "2026-04-24")]
lemma iSup_iInf_eq (f : ∀ i, κ i → α) :
    let _ := minAx.toLattice; let := ofMinimalAxioms minAx
    ⨆ i, ⨅ j, f i j = ⨅ g : ∀ i, κ i, ⨆ i, f i (g i) :=
  let _ := minAx.toLattice; let := ofMinimalAxioms minAx
  _root_.iSup_iInf_eq f

/-- The `CompletelyDistribLattice.MinimalAxioms` element corresponding to a frame. -/
@[implicit_reducible]
def of [Lattice α] [CompletelyDistribLattice α] : MinimalAxioms α :=
  { ‹CompletelyDistribLattice α› with }

end MinimalAxioms

end CompletelyDistribLattice

theorem biSup_iInter_of_pairwise_disjoint [Lattice α] [OrderBot α] [CompletelyDistribLattice α]
    {ι κ : Type*} [hκ : Nonempty κ] {f : ι → α} (h : Pairwise (Disjoint on f)) (s : κ → Set ι) :
    (⨆ i ∈ (⋂ j, s j), f i) = ⨅ j, (⨆ i ∈ s j, f i) := by
  rcases hκ with ⟨j⟩
  simp_rw [iInf_iSup_eq, mem_iInter]
  refine le_antisymm
    (iSup₂_le fun i hi ↦ le_iSup₂_of_le (fun _ ↦ i) hi (le_iInf fun _ ↦ le_rfl))
    (iSup₂_le fun I hI ↦ ?_)
  by_cases! H : ∀ k, I k = I j
  · exact le_iSup₂_of_le (I j) (fun k ↦ (H k) ▸ (hI k)) (iInf_le _ _)
  · rcases H with ⟨k, hk⟩
    calc ⨅ l, f (I l)
    _ ≤ f (I k) ⊓ f (I j) := le_inf (iInf_le _ _) (iInf_le _ _)
    _ = ⊥ := (h hk).eq_bot
    _ ≤ _ := bot_le

-- See note [lower instance priority]
instance (priority := 100) LinearOrder.toCompletelyDistribLattice
    [LinearOrder α] [CompleteLattice α] :
    CompletelyDistribLattice α where
  iInf_iSup_eq {α β} g := by
    let lhs := ⨅ a, ⨆ b, g a b
    let rhs := ⨆ h : ∀ a, β a, ⨅ a, g a (h a)
    suffices lhs ≤ rhs from le_antisymm this le_iInf_iSup
    if h : ∃ x, rhs < x ∧ x < lhs then
      rcases h with ⟨x, hr, hl⟩
      suffices rhs ≥ x from nomatch not_lt.2 this hr
      have : ∀ a, ∃ b, x < g a b := fun a =>
        lt_iSup_iff.1 <| lt_of_not_ge fun h =>
            lt_irrefl x (lt_of_lt_of_le hl (le_trans (iInf_le _ a) h))
      choose f hf using this
      refine le_trans ?_ (le_iSup _ f)
      exact le_iInf fun a => le_of_lt (hf a)
    else
      refine le_of_not_gt fun hrl : rhs < lhs => not_le_of_gt hrl ?_
      replace h : ∀ x, x ≤ rhs ∨ lhs ≤ x := by
        simpa only [not_exists, not_and_or, not_or, not_lt] using h
      have : ∀ a, ∃ b, rhs < g a b := fun a =>
        lt_iSup_iff.1 <| lt_of_lt_of_le hrl (iInf_le _ a)
      choose f hf using this
      have : ∀ a, lhs ≤ g a (f a) := fun a =>
        (h (g a (f a))).resolve_left (by simpa using hf a)
      refine le_trans ?_ (le_iSup _ f)
      exact le_iInf fun a => this _

section Frame

section Lattice

variable [Lattice α] [Frame α] {s t : Set α} {a b c d : α}

attribute [local instance]
  HeytingAlgebra.ofFrame BoundedOrder.mk OrderBot.ofSupSet OrderTop.ofInfSet in
instance OrderDual.instCoframe : Coframe αᵒᵈ := fast_instance% .ofCoheytingAlgebra

theorem iSup₂_inf_eq {f : ∀ i, κ i → α} (a : α) :
    (⨆ (i) (j), f i j) ⊓ a = ⨆ (i) (j), f i j ⊓ a := by
  simp only [iSup_inf_eq]

theorem iSup_inf_iSup {ι ι' : Type*} {f : ι → α} {g : ι' → α} :
    ((⨆ i, f i) ⊓ ⨆ j, g j) = ⨆ i : ι × ι', f i.1 ⊓ g i.2 := by
  simp_rw [iSup_inf_eq, inf_iSup_eq, iSup_prod]

theorem biSup_inf_biSup {ι ι' : Type*} {f : ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'} :
    ((⨆ i ∈ s, f i) ⊓ ⨆ j ∈ t, g j) = ⨆ p ∈ s ×ˢ t, f (p : ι × ι').1 ⊓ g p.2 := by
  simp only [iSup_subtype', iSup_inf_iSup]
  exact (Equiv.surjective _).iSup_congr (Equiv.Set.prod s t).symm fun x => rfl

theorem sSup_inf_sSup : sSup s ⊓ sSup t = ⨆ p ∈ s ×ˢ t, (p : α × α).1 ⊓ p.2 := by
  simp only [sSup_eq_iSup, biSup_inf_biSup]

section
variable [OrderBot α]

theorem biSup_inter_of_pairwise_disjoint {ι : Type*} {f : ι → α}
    (h : Pairwise (Disjoint on f)) (s t : Set ι) :
    (⨆ i ∈ (s ∩ t), f i) = (⨆ i ∈ s, f i) ⊓ (⨆ i ∈ t, f i) := by
  rw [biSup_inf_biSup]
  refine le_antisymm
    (iSup₂_le fun i ⟨his, hit⟩ ↦ le_iSup₂_of_le ⟨i, i⟩ ⟨his, hit⟩ (le_inf le_rfl le_rfl))
    (iSup₂_le fun ⟨i, j⟩ ⟨his, hjs⟩ ↦ ?_)
  by_cases hij : i = j
  · exact le_iSup₂_of_le i ⟨his, hij ▸ hjs⟩ inf_le_left
  · simp [h hij |>.eq_bot]

theorem iSup_disjoint_iff {f : ι → α} : Disjoint (⨆ i, f i) a ↔ ∀ i, Disjoint (f i) a := by
  simp only [disjoint_iff, iSup_inf_eq, iSup_eq_bot]

theorem disjoint_iSup_iff {f : ι → α} : Disjoint a (⨆ i, f i) ↔ ∀ i, Disjoint a (f i) := by
  simpa only [disjoint_comm] using @iSup_disjoint_iff

theorem iSup₂_disjoint_iff {f : ∀ i, κ i → α} :
    Disjoint (⨆ (i) (j), f i j) a ↔ ∀ i j, Disjoint (f i j) a := by
  simp_rw [iSup_disjoint_iff]

theorem disjoint_iSup₂_iff {f : ∀ i, κ i → α} :
    Disjoint a (⨆ (i) (j), f i j) ↔ ∀ i j, Disjoint a (f i j) := by
  simp_rw [disjoint_iSup_iff]

theorem sSup_disjoint_iff {s : Set α} : Disjoint (sSup s) a ↔ ∀ b ∈ s, Disjoint b a := by
  simp only [disjoint_iff, sSup_inf_eq, iSup_eq_bot]

theorem disjoint_sSup_iff {s : Set α} : Disjoint a (sSup s) ↔ ∀ b ∈ s, Disjoint a b := by
  simpa only [disjoint_comm] using @sSup_disjoint_iff

end

theorem iSup_inf_of_monotone {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f g : ι → α}
    (hf : Monotone f) (hg : Monotone g) : ⨆ i, f i ⊓ g i = (⨆ i, f i) ⊓ ⨆ i, g i := by
  refine (le_iSup_inf_iSup f g).antisymm ?_
  rw [iSup_inf_iSup]
  refine iSup_mono' fun i => ?_
  rcases directed_of (· ≤ ·) i.1 i.2 with ⟨j, h₁, h₂⟩
  exact ⟨j, inf_le_inf (hf h₁) (hg h₂)⟩

theorem iSup_inf_of_antitone {ι : Type*} [Preorder ι] [IsCodirectedOrder ι] {f g : ι → α}
    (hf : Antitone f) (hg : Antitone g) : ⨆ i, f i ⊓ g i = (⨆ i, f i) ⊓ ⨆ i, g i :=
  iSup_inf_of_monotone (ι := ιᵒᵈ) hf.dual_left hg.dual_left

-- see Note [lower instance priority]
instance (priority := 100) Frame.toDistribLattice : DistribLattice α :=
  DistribLattice.ofInfSupLe fun a b c => by
    rw [← sSup_pair, ← sSup_pair, inf_sSup_eq, ← sSup_image, image_pair]

attribute [local instance]
  HeytingAlgebra.ofFrame BoundedOrder.mk OrderBot.ofSupSet OrderTop.ofInfSet in
instance Prod.instFrame [Lattice β] [Frame β] : Frame (α × β) :=
  fast_instance% .ofHeytingAlgebra

attribute [local instance]
  HeytingAlgebra.ofFrame BoundedOrder.mk OrderBot.ofSupSet OrderTop.ofInfSet in
instance Pi.instFrame {ι : Type*} {π : ι → Type*} [∀ i, Lattice (π i)] [∀ i, Frame (π i)] :
    Frame (∀ i, π i) :=
  fast_instance% .ofHeytingAlgebra

end Lattice

section HeytingAlgebra

variable [HeytingAlgebra α] [Frame α] {a b c : α}

theorem himp_iInf_eq {f : ι → α} : a ⇨ (⨅ x, f x) = ⨅ x, a ⇨ f x :=
  eq_of_forall_le_iff fun b => by simp

theorem iSup_himp_eq {f : ι → α} : (⨆ x, f x) ⇨ a = ⨅ x, f x ⇨ a :=
  eq_of_forall_le_iff fun b => by simp [inf_iSup_eq]

theorem himp_eq_sSup : a ⇨ b = sSup {w | w ⊓ a ≤ b} :=
  (isGreatest_himp a b).isLUB.sSup_eq.symm

theorem compl_eq_sSup_disjoint : aᶜ = sSup {w | Disjoint w a} :=
  (isGreatest_compl a).isLUB.sSup_eq.symm

lemma himp_le_iff : a ⇨ b ≤ c ↔ ∀ d, d ⊓ a ≤ b → d ≤ c := by simp [himp_eq_sSup]

end HeytingAlgebra

end Frame

section Coframe

section Lattice

variable [Lattice α] [Coframe α] {s t : Set α} {a b c d : α}

attribute [local instance]
  CoheytingAlgebra.ofCoframe BoundedOrder.mk OrderBot.ofSupSet OrderTop.ofInfSet in
instance OrderDual.instFrame : Frame αᵒᵈ := fast_instance% .ofHeytingAlgebra

theorem iInf₂_sup_eq {f : ∀ i, κ i → α} (a : α) : (⨅ (i) (j), f i j) ⊔ a = ⨅ (i) (j), f i j ⊔ a :=
  @iSup₂_inf_eq αᵒᵈ _ _ _ _ _ _

theorem iInf_sup_iInf {ι ι' : Type*} {f : ι → α} {g : ι' → α} :
    ((⨅ i, f i) ⊔ ⨅ i, g i) = ⨅ i : ι × ι', f i.1 ⊔ g i.2 :=
  @iSup_inf_iSup αᵒᵈ _ _ _ _ _ _

theorem biInf_sup_biInf {ι ι' : Type*} {f : ι → α} {g : ι' → α} {s : Set ι} {t : Set ι'} :
    ((⨅ i ∈ s, f i) ⊔ ⨅ j ∈ t, g j) = ⨅ p ∈ s ×ˢ t, f (p : ι × ι').1 ⊔ g p.2 :=
  @biSup_inf_biSup αᵒᵈ _ _ _ _ _ _ _ _

theorem sInf_sup_sInf : sInf s ⊔ sInf t = ⨅ p ∈ s ×ˢ t, (p : α × α).1 ⊔ p.2 :=
  @sSup_inf_sSup αᵒᵈ _ _ _ _

@[to_dual existing]
theorem iInf_sup_of_monotone {ι : Type*} [Preorder ι] [IsCodirectedOrder ι] {f g : ι → α}
    (hf : Monotone f) (hg : Monotone g) : ⨅ i, f i ⊔ g i = (⨅ i, f i) ⊔ ⨅ i, g i :=
  @iSup_inf_of_antitone αᵒᵈ _ _ _ _ _ _ _ hf.dual_right hg.dual_right

theorem iInf_sup_of_antitone {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f g : ι → α}
    (hf : Antitone f) (hg : Antitone g) : ⨅ i, f i ⊔ g i = (⨅ i, f i) ⊔ ⨅ i, g i :=
  @iSup_inf_of_monotone αᵒᵈ _ _ _ _ _ _ _ hf.dual_right hg.dual_right

-- see Note [lower instance priority]
instance (priority := 100) Coframe.toDistribLattice : DistribLattice α where
  __ := ‹Coframe α›
  le_sup_inf a b c := by
    rw [← sInf_pair, ← sInf_pair, sup_sInf_eq, ← sInf_image, image_pair]

attribute [local instance]
  CoheytingAlgebra.ofCoframe BoundedOrder.mk OrderBot.ofSupSet OrderTop.ofInfSet in
instance Prod.instCoframe [Lattice β] [Coframe β] : Coframe (α × β) :=
  fast_instance% .ofCoheytingAlgebra

attribute [local instance]
  CoheytingAlgebra.ofCoframe BoundedOrder.mk OrderBot.ofSupSet OrderTop.ofInfSet in
instance Pi.instCoframe {ι : Type*} {π : ι → Type*} [∀ i, Lattice (π i)] [∀ i, Coframe (π i)] :
    Coframe (∀ i, π i) :=
  fast_instance% .ofCoheytingAlgebra

end Lattice

section CoheytingAlgebra

variable [CoheytingAlgebra α] [Coframe α] {s t : Set α} {a b c d : α}

theorem iSup_sdiff_eq {f : ι → α} : (⨆ x, f x) \ a = ⨆ x, f x \ a :=
  eq_of_forall_ge_iff fun _ => by simp

theorem sdiff_iSup_eq {f : ι → α} : a \ ⨅ x, f x = ⨆ x, a \ f x :=
  eq_of_forall_ge_iff fun _ => by simp [iInf_sup_eq]

theorem sdiff_eq_sInf : a \ b = sInf {w | a ≤ b ⊔ w} :=
  (isLeast_sdiff a b).isGLB.sInf_eq.symm

theorem hnot_eq_sInf_codisjoint : ￢a = sInf {w | Codisjoint a w} :=
  (isLeast_hnot a).isGLB.sInf_eq.symm

lemma le_sdiff_iff : a ≤ b \ c ↔ ∀ d, b ≤ c ⊔ d → a ≤ d := by simp [sdiff_eq_sInf]

end CoheytingAlgebra

end Coframe

section CompleteDistribLattice

instance OrderDual.instCompleteDistribLattice [Lattice α] [CompleteDistribLattice α] :
    CompleteDistribLattice αᵒᵈ where
  __ := instFrame
  __ := instCoframe

instance Prod.instCompleteDistribLattice [Lattice α] [CompleteDistribLattice α]
    [Lattice β] [CompleteDistribLattice β] :
    CompleteDistribLattice (α × β) where
  __ := instFrame
  __ := instCoframe

instance Pi.instCompleteDistribLattice {ι : Type*} {π : ι → Type*}
    [∀ i, Lattice (π i)] [∀ i, CompleteDistribLattice (π i)] :
    CompleteDistribLattice (∀ i, π i) where
  __ := instFrame
  __ := instCoframe

end CompleteDistribLattice

section CompletelyDistribLattice

instance OrderDual.instCompletelyDistribLattice [Lattice α] [CompletelyDistribLattice α] :
    CompletelyDistribLattice αᵒᵈ where
  iInf_iSup_eq := iSup_iInf_eq (α := α)

instance Prod.instCompletelyDistribLattice [Lattice α] [CompletelyDistribLattice α]
    [Lattice β] [CompletelyDistribLattice β] : CompletelyDistribLattice (α × β) where
  iInf_iSup_eq f := by ext <;> simp [fst_iSup, fst_iInf, snd_iSup, snd_iInf, iInf_iSup_eq]

instance Pi.instCompletelyDistribLattice {ι : Type*} {π : ι → Type*}
    [∀ i, Lattice (π i)] [∀ i, CompletelyDistribLattice (π i)] :
    CompletelyDistribLattice (∀ i, π i) where
  iInf_iSup_eq f := by ext i; simp only [iInf_apply, iSup_apply, iInf_iSup_eq]

end CompletelyDistribLattice

/--
A complete Boolean algebra is a Boolean algebra that is also a complete distributive lattice.

It is only completely distributive if it is also atomic.
-/
@[deprecated "Use `[BooleanAlgebra α] [CompleteLattice α]` instead" (since := "2026-04-24")]
class CompleteBooleanAlgebra (α) extends BooleanAlgebra α, CompleteLattice α

section CompleteBooleanAlgebra

variable [BooleanAlgebra α] [CompleteLattice α] {s : Set α} {f : ι → α}

theorem compl_iInf : (iInf f)ᶜ = ⨆ i, (f i)ᶜ :=
  le_antisymm
    (compl_le_of_compl_le <| le_iInf fun i => compl_le_of_compl_le <|
      le_iSup (Compl.compl ∘ f) i)
    (iSup_le fun _ => compl_le_compl <| iInf_le _ _)

theorem compl_iSup : (iSup f)ᶜ = ⨅ i, (f i)ᶜ :=
  compl_injective (by simp [compl_iInf])

theorem compl_sInf : (sInf s)ᶜ = ⨆ i ∈ s, iᶜ := by simp only [sInf_eq_iInf, compl_iInf]

theorem compl_sSup : (sSup s)ᶜ = ⨅ i ∈ s, iᶜ := by simp only [sSup_eq_iSup, compl_iSup]

theorem compl_sInf' : (sInf s)ᶜ = sSup (Compl.compl '' s) :=
  compl_sInf.trans sSup_image.symm

theorem compl_sSup' : (sSup s)ᶜ = sInf (Compl.compl '' s) :=
  compl_sSup.trans sInf_image.symm

open scoped symmDiff in
/-- The symmetric difference of two `iSup`s is at most the `iSup` of the symmetric differences. -/
theorem iSup_symmDiff_iSup_le {g : ι → α} : (⨆ i, f i) ∆ (⨆ i, g i) ≤ ⨆ i, ((f i) ∆ (g i)) := by
  simp_rw [symmDiff_le_iff, ← iSup_sup_eq]
  exact ⟨iSup_mono fun i ↦ sup_comm (g i) _ ▸ le_symmDiff_sup_right ..,
    iSup_mono fun i ↦ sup_comm (f i) _ ▸ symmDiff_comm (f i) _ ▸ le_symmDiff_sup_right ..⟩

open scoped symmDiff in
/-- A `biSup` version of `iSup_symmDiff_iSup_le`. -/
theorem biSup_symmDiff_biSup_le {p : ι → Prop} {f g : (i : ι) → p i → α} :
    (⨆ i, ⨆ (h : p i), f i h) ∆ (⨆ i, ⨆ (h : p i), g i h) ≤
    ⨆ i, ⨆ (h : p i), ((f i h) ∆ (g i h)) :=
  le_trans iSup_symmDiff_iSup_le <| iSup_mono fun _ ↦ iSup_symmDiff_iSup_le

end CompleteBooleanAlgebra

set_option linter.deprecated false in
/--
A complete atomic Boolean algebra is a complete Boolean algebra
that is also completely distributive.

We take iSup_iInf_eq as the definition here,
and prove later on that this implies atomicity.
-/
@[deprecated "Use `[BooleanAlgebra α] [CompletelyDistribLattice α]` instead"
  (since := "2026-04-24")]
class CompleteAtomicBooleanAlgebra (α : Type u) extends CompleteBooleanAlgebra α where
  protected iInf_iSup_eq {ι : Type u} {κ : ι → Type u} (f : ∀ a, κ a → α) :
    (⨅ a, ⨆ b, f a b) = ⨆ g : ∀ a, κ a, ⨅ a, f a (g a)

instance Prop.instCompletelyDistribLattice : CompletelyDistribLattice Prop where
  iInf_iSup_eq f := by simp [Classical.skolem]

section lift

-- See note [reducible non-instances]
/-- Pullback an `Order.Frame`. -/
protected abbrev Frame.lift [Lattice α] [SupSet α] [InfSet α] [Lattice β] [Frame β]
    (f : α → β) (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a) :
    Frame α where
  toCompleteLattice := .lift f le map_sSup map_sInf
  inf_sSup_le_iSup_inf a s := by
    let : CompleteLattice α := .lift f le map_sSup map_sInf
    have map_inf a b : f (a ⊓ b) = f a ⊓ f b := by
      rw [← sInf_pair, ← sInf_pair, map_sInf, ← image_pair, sInf_image]
    rw [← le, ← sSup_image, map_inf, map_sSup s, inf_iSup₂_eq]
    simp_rw [← map_inf]
    exact ((map_sSup _).trans iSup_image).ge

-- See note [reducible non-instances]
/-- Pullback an `Order.Coframe`. -/
protected abbrev Coframe.lift [Lattice α] [SupSet α] [InfSet α] [Lattice β] [Coframe β]
    (f : α → β) (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a) :
    Coframe α where
  toCompleteLattice := .lift f le map_sSup map_sInf
  iInf_sup_le_sup_sInf a s := by
    let : CompleteLattice α := .lift f le map_sSup map_sInf
    have map_sup a b : f (a ⊔ b) = f a ⊔ f b := by
      rw [← sSup_pair, ← sSup_pair, map_sSup, ← image_pair, sSup_image]
    rw [← le, ← sInf_image, map_sup, map_sInf s, sup_iInf₂_eq]
    simp_rw [← map_sup]
    exact ((map_sInf _).trans iInf_image).le

-- See note [reducible non-instances]
/-- Pullback a `CompleteDistribLattice`. -/
protected abbrev CompleteDistribLattice.lift [Lattice α] [SupSet α] [InfSet α]
    [Lattice β] [CompleteDistribLattice β]
    (f : α → β) (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a) :
    CompleteDistribLattice α where
  __ := Frame.lift f le map_sSup map_sInf
  __ := Coframe.lift f le map_sSup map_sInf

-- See note [reducible non-instances]
/-- Pullback a `CompletelyDistribLattice` along an injection. -/
protected abbrev CompletelyDistribLattice.lift [Lattice α] [SupSet α] [InfSet α]
    [Lattice β] [CompletelyDistribLattice β]
    (f : α → β) (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a) :
    CompletelyDistribLattice α where
  __ := CompleteLattice.lift f le map_sSup map_sInf
  iInf_iSup_eq g := by
    have hf : f.Injective := fun _ _ ↦ by simp [le_antisymm_iff, le]
    apply hf
    simp_rw [iInf, map_sInf, iInf_range, iSup, map_sSup, iSup_range, map_sInf, iInf_range,
      iInf_iSup_eq]

@[deprecated (since := "2026-04-24")]
protected alias Function.Injective.frameMinimalAxioms := Frame.lift
@[deprecated (since := "2026-04-24")]
protected alias Function.Injective.coframeMinimalAxioms := Coframe.lift
@[deprecated (since := "2026-04-24")]
protected alias Function.Injective.frame := Frame.lift
@[deprecated (since := "2026-04-24")]
protected alias Function.Injective.coframe := Coframe.lift
@[deprecated (since := "2026-04-24")]
protected alias Function.Injective.completeDistribLatticeMinimalAxioms :=
  CompleteDistribLattice.lift
@[deprecated (since := "2026-04-24")]
protected alias Function.Injective.completeDistribLattice := CompleteDistribLattice.lift
@[deprecated (since := "2026-04-24")]
protected alias Function.Injective.completelyDistribLatticeMinimalAxioms :=
  CompletelyDistribLattice.lift
@[deprecated (since := "2026-04-24")]
protected alias Function.Injective.completelyDistribLattice := CompletelyDistribLattice.lift
@[deprecated (since := "2026-04-24")]
protected alias Function.Injective.completeBooleanAlgebra := CompleteLattice.lift
@[deprecated (since := "2026-04-24")]
protected alias Function.Injective.completeAtomicBooleanAlgebra := CompletelyDistribLattice.lift

namespace Equiv

variable (e : α ≃ β)

/-- Transfer `Frame` across an `Equiv`. -/
protected abbrev frame [Lattice β] [Frame β] : letI := e.lattice; Frame α := by
  letI := e.lattice
  letI completeLattice := e.completeLattice
  apply Frame.lift e <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `Coframe` across an `Equiv`. -/
protected abbrev coframe [Lattice β] [Coframe β] : letI := e.lattice; Coframe α := by
  letI := e.lattice
  letI completeLattice := e.completeLattice
  apply Coframe.lift e <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `CompleteDistribLattice` across an `Equiv`. -/
protected abbrev completeDistribLattice [Lattice β] [CompleteDistribLattice β] :
    letI := e.lattice
    CompleteDistribLattice α := by
  letI := e.lattice
  letI completeLattice := e.completeLattice
  apply CompleteDistribLattice.lift e <;> intros <;> first | rfl | exact e.apply_symm_apply _

/-- Transfer `CompletelyDistribLattice` across an `Equiv`. -/
protected abbrev completelyDistribLattice [Lattice β] [CompletelyDistribLattice β] :
    letI := e.lattice
    CompletelyDistribLattice α := by
  letI := e.lattice
  letI completeDistribLattice := e.completeDistribLattice
  apply CompletelyDistribLattice.lift e <;> intros <;> first | rfl | exact e.apply_symm_apply _

@[deprecated (since := "2026-04-24")]
protected alias completeBooleanAlgebra := Equiv.completeLattice
@[deprecated (since := "2026-04-24")]
protected alias completeAtomicBooleanAlgebra := Equiv.completelyDistribLattice

end Equiv

end lift

namespace PUnit

variable (s : Set PUnit.{u + 1})

@[simp]
theorem sSup_eq : sSup s = unit :=
  rfl

@[simp]
theorem sInf_eq : sInf s = unit :=
  rfl

end PUnit
