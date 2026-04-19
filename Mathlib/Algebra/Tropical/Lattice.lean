/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!

# Order on tropical algebraic structure

This file defines the orders induced on tropical algebraic structures by the underlying type.

## Main declarations

* `ConditionallyCompleteLattice (Tropical R)`
* `ConditionallyCompleteLinearOrder (Tropical R)`

## Implementation notes

The order induced is the definitionally equal underlying order, which makes the proofs and
constructions quicker to implement.

-/

@[expose] public section


variable {R S : Type*}

open Tropical

instance instSemilatticeInfTropical [SemilatticeInf R] : SemilatticeInf (Tropical R) :=
  { Tropical.instPartialOrderTropical with
    inf := fun x y ↦ trop (untrop x ⊓ untrop y)
    le_inf := fun _ _ _ ↦ @SemilatticeInf.le_inf R _ _ _ _
    inf_le_left := fun _ _ ↦ inf_le_left
    inf_le_right := fun _ _ ↦ inf_le_right }

instance instSemilatticeSupTropical [SemilatticeSup R] : SemilatticeSup (Tropical R) :=
  { Tropical.instPartialOrderTropical with
    sup := fun x y ↦ trop (untrop x ⊔ untrop y)
    sup_le := fun _ _ _ ↦ @SemilatticeSup.sup_le R _ _ _ _
    le_sup_left := fun _ _ ↦ le_sup_left
    le_sup_right := fun _ _ ↦ le_sup_right }

instance instLatticeTropical [Lattice R] : Lattice (Tropical R) :=
  { instSemilatticeInfTropical, instSemilatticeSupTropical with }

instance instConditionallyCompleteLatticeTropical [ConditionallyCompleteLattice R] :
    ConditionallyCompleteLattice (Tropical R) where
  exists_isLUB_cond s hn hb :=
    ⟨trop (sSup (untrop '' s)),
      .of_image untrop_le_iff <| isLUB_csSup (hn.image _) (untrop_monotone.map_bddAbove hb)⟩
  exists_isGLB_cond s hn hb :=
    ⟨trop (sInf (untrop '' s)),
      .of_image untrop_le_iff <| isGLB_csInf (hn.image _) (untrop_monotone.map_bddBelow hb)⟩

instance [ConditionallyCompleteLinearOrder R] : ConditionallyCompleteLinearOrder (Tropical R) :=
  { instConditionallyCompleteLatticeTropical, Tropical.instLinearOrderTropical with }
