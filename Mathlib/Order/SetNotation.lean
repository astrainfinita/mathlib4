/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Yury Kudryashov, Yuyang Zhao
-/
module

public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Util.Notation3

/-!
# Notation classes for set supremum and infimum

In this file we introduce notation for indexed suprema, infima, unions, and intersections.

## Main definitions

- `sSup s`, `sInf s`: supremum and infimum of the set `s`;
- `iSup f`, `iInf f`: supremum and infimum of an indexed family of elements,
  defined as `sSup (Set.range f)` and `sInf (Set.range f)`, respectively;
- `Set.sUnion s`, `Set.sInter s`: same as `sSup s` and `sInf s`,
  but works only for sets of sets;
- `Set.iUnion s`, `Set.iInter s`: same as `iSup s` and `iInf s`,
  but works only for indexed families of sets.

## Notation

- `⨆ i, f i`, `⨅ i, f i`: supremum and infimum of an indexed family, respectively;
- `⋃₀ s`, `⋂₀ s`: union and intersection of a set of sets;
- `⋃ i, s i`, `⋂ i, s i`: union and intersection of an indexed family of sets.

-/

@[expose] public section

noncomputable section

open Set

universe u v
variable {α : Type u} {ι : Sort v}

open Classical in
/-- Supremum of a set -/
@[to_dual /-- Infimum of a set -/]
def sSup [LE α] [Nonempty α] (s : Set α) : α :=
  if h : ∃ x, IsLUB s x then Classical.choose h else Classical.arbitrary α

/-- Indexed supremum -/
@[to_dual /-- Indexed infimum -/]
def iSup [LE α] [Nonempty α] (s : ι → α) : α :=
  sSup (range s)

/-- Indexed supremum. -/
notation3 "⨆ " (...)", " r:60:(scoped f => iSup f) => r

/-- Indexed infimum. -/
notation3 "⨅ " (...)", " r:60:(scoped f => iInf f) => r

section delaborators

open Lean Lean.PrettyPrinter.Delaborator

/-- Delaborator for indexed supremum. -/
@[app_delab iSup]
meta def iSup_delab : Delab := whenPPOption Lean.getPPNotation <| withOverApp 4 do
  let #[_, ι, _, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(⨆ (_ : $dom), $body)
      else if prop || ppTypes then
        `(⨆ ($x:ident : $dom), $body)
      else
        `(⨆ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(⨆ $x:ident, ⨆ (_ : $y:ident ∈ $s), $body)
    | `(⨆ ($x:ident : $_), ⨆ (_ : $y:ident ∈ $s), $body) =>
      if x == y then `(⨆ $x:ident ∈ $s, $body) else pure stx
    | _ => pure stx
  return stx

/-- Delaborator for indexed infimum. -/
@[app_delab iInf]
meta def iInf_delab : Delab := whenPPOption Lean.getPPNotation <| withOverApp 4 do
  let #[_, ι, _, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(⨅ (_ : $dom), $body)
      else if prop || ppTypes then
        `(⨅ ($x:ident : $dom), $body)
      else
        `(⨅ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(⨅ $x:ident, ⨅ (_ : $y:ident ∈ $s), $body)
    | `(⨅ ($x:ident : $_), ⨅ (_ : $y:ident ∈ $s), $body) =>
      if x == y then `(⨅ $x:ident ∈ $s, $body) else pure stx
    | _ => pure stx
  return stx
end delaborators

@[to_dual]
theorem exists_isLUB_iff_isLUB_sSup [LE α] [Nonempty α] {s : Set α} :
    (∃ a, IsLUB s a) ↔ IsLUB s (sSup s) := by
  constructor
  · intro h
    rw [sSup, dif_pos h]
    exact Classical.choose_spec _
  · exact fun h ↦ ⟨_, h⟩

@[to_dual] alias ⟨isLUB_sSup_of_exists_isLUB, _⟩ := exists_isLUB_iff_isLUB_sSup

@[to_dual]
theorem IsLUB.sSup_eq [PartialOrder α] [Nonempty α] {s : Set α} {a : α} (h : IsLUB s a) :
    sSup s = a :=
  (isLUB_sSup_of_exists_isLUB ⟨a, h⟩).unique h

@[to_dual]
theorem IsLUB.iSup_eq [PartialOrder α] [Nonempty α] {f : ι → α} {a : α} (h : IsLUB (.range f) a) :
    iSup f = a :=
  h.sSup_eq

@[to_dual]
theorem sSup_of_not_bddAbove [Preorder α] [Nonempty α] {s : Set α}
    (hs : ¬BddAbove s) : sSup s = Classical.arbitrary α :=
  dif_neg (fun ⟨_, hx⟩ ↦ hs hx.bddAbove)

namespace Set

/-
We don't translate the order on sets (i.e. turning `s ⊆ t` into `t ⊆ s`).
This is because for example the following theorems should be dual
```
theorem sSup_le_sSup {s t : Set α} (h : s ⊆ t) : sSup s ≤ sSup t
theorem sInf_le_sInf {s t : Set α} (h : s ⊆ t) : sInf t ≤ sInf s
```
Additionally, dualizing the order on sets would mean that a set is dual to its complement.
But we would like to dualize set intervals such that e.g. `Ico a b` is dual to `Ioc b a`.
-/
attribute [to_dual_dont_translate] Set

/-- Intersection of a set of sets. -/
def sInter (S : Set (Set α)) : Set α :=
  { a | ∀ t ∈ S, a ∈ t }

/-- Notation for `Set.sInter` Intersection of a set of sets. -/
prefix:110 "⋂₀ " => sInter

/-- Union of a set of sets. -/
def sUnion (S : Set (Set α)) : Set α :=
  { a | ∃ t ∈ S, a ∈ t }

/-- Notation for `Set.sUnion`. Union of a set of sets. -/
prefix:110 "⋃₀ " => sUnion

@[simp, grind =, push]
theorem mem_sInter {x : α} {S : Set (Set α)} : x ∈ ⋂₀ S ↔ ∀ t ∈ S, x ∈ t :=
  Iff.rfl

@[simp, grind =, push]
theorem mem_sUnion {x : α} {S : Set (Set α)} : x ∈ ⋃₀ S ↔ ∃ t ∈ S, x ∈ t :=
  Iff.rfl

/-- Indexed union of a family of sets -/
def iUnion (s : ι → Set α) : Set α :=
  sUnion (range s)

/-- Indexed intersection of a family of sets -/
def iInter (s : ι → Set α) : Set α :=
  sInter (range s)

/-- Notation for `Set.iUnion`. Indexed union of a family of sets -/
notation3 "⋃ " (...)", " r:60:(scoped f => iUnion f) => r

/-- Notation for `Set.iInter`. Indexed intersection of a family of sets -/
notation3 "⋂ " (...)", " r:60:(scoped f => iInter f) => r

section delaborators

open Lean Lean.PrettyPrinter.Delaborator

/-- Delaborator for indexed unions. -/
@[app_delab Set.iUnion]
meta def iUnion_delab : Delab := whenPPOption Lean.getPPNotation do
  let #[_, ι, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(⋃ (_ : $dom), $body)
      else if prop || ppTypes then
        `(⋃ ($x:ident : $dom), $body)
      else
        `(⋃ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(⋃ $x:ident, ⋃ (_ : $y:ident ∈ $s), $body)
    | `(⋃ ($x:ident : $_), ⋃ (_ : $y:ident ∈ $s), $body) =>
      if x == y then `(⋃ $x:ident ∈ $s, $body) else pure stx
    | _ => pure stx
  return stx

/-- Delaborator for indexed intersections. -/
@[app_delab Set.iInter]
meta def sInter_delab : Delab := whenPPOption Lean.getPPNotation do
  let #[_, ι, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(⋂ (_ : $dom), $body)
      else if prop || ppTypes then
        `(⋂ ($x:ident : $dom), $body)
      else
        `(⋂ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(⋂ $x:ident, ⋂ (_ : $y:ident ∈ $s), $body)
    | `(⋂ ($x:ident : $_), ⋂ (_ : $y:ident ∈ $s), $body) =>
      if x == y then `(⋂ $x:ident ∈ $s, $body) else pure stx
    | _ => pure stx
  return stx

end delaborators

@[simp, push]
theorem mem_iUnion {x : α} {s : ι → Set α} : (x ∈ ⋃ i, s i) ↔ ∃ i, x ∈ s i :=
  ⟨fun ⟨_, ⟨⟨a, (t_eq : s a = _)⟩, (h : x ∈ _)⟩⟩ => ⟨a, t_eq.symm ▸ h⟩, fun ⟨a, h⟩ =>
    ⟨s a, ⟨⟨a, rfl⟩, h⟩⟩⟩

@[simp, push]
theorem mem_iInter {x : α} {s : ι → Set α} : (x ∈ ⋂ i, s i) ↔ ∀ i, x ∈ s i :=
  ⟨fun (h : ∀ a ∈ { a : Set α | ∃ i, s i = a }, x ∈ a) a => h (s a) ⟨a, rfl⟩,
    fun h _ ⟨a, (eq : s a = _)⟩ => eq ▸ h a⟩

theorem isLUB_sUnion (S : Set (Set α)) : IsLUB S (⋃₀ S) :=
  ⟨fun s hs _ hx ↦ ⟨s, hs, hx⟩, fun _ h _ ⟨_, ⟨hs, hx⟩⟩ => h hs hx⟩

theorem isGLB_sInter (S : Set (Set α)) : IsGLB S (⋂₀ S) :=
  ⟨fun _ hs _ hx ↦ hx _ hs, fun _ h _ hx _ hs => h hs hx⟩

@[simp]
theorem sSup_eq_sUnion (S : Set (Set α)) : sSup S = ⋃₀ S :=
  (isLUB_sUnion S).sSup_eq

@[simp]
theorem sInf_eq_sInter (S : Set (Set α)) : sInf S = ⋂₀ S :=
  (isGLB_sInter S).sInf_eq

@[simp]
theorem iSup_eq_iUnion (s : ι → Set α) : iSup s = iUnion s := by
  simp [iSup, iUnion]

@[simp]
theorem iInf_eq_iInter (s : ι → Set α) : iInf s = iInter s := by
  simp [iInf, iInter]

end Set
