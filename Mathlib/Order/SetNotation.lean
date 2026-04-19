/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Yury Kudryashov, Yuyang Zhao
-/
module

public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Bounds.Defs
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
  Classical.epsilon (IsLUB s)

/-- Indexed supremum -/
@[to_dual /-- Indexed infimum -/]
def iSup [LE α] [Nonempty α] (s : ι → α) : α :=
  sSup (range s)

/-- Class for the `sSup` operator -/
structure SupSet (α : Type*) where
  /-- Supremum of a set -/
  sSup : Set α → α

/-- Class for the `sInf` operator -/
@[to_dual existing]
structure InfSet (α : Type*) where
  /-- Infimum of a set -/
  sInf : Set α → α

attribute [deprecated sSup (since := "2026-04-06")] SupSet
attribute [deprecated sInf (since := "2026-04-06")] InfSet

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
theorem isLUB_sSup_of_isLUB [LE α] [Nonempty α] {s : Set α} {a : α} (h : IsLUB s a) :
    IsLUB s (sSup s) :=
  Classical.epsilon_spec ⟨_, h⟩

@[to_dual] protected alias IsLUB.isLUB_sSup := isLUB_sSup_of_isLUB

@[to_dual]
theorem exists_isLUB_iff_isLUB_sSup [LE α] [Nonempty α] {s : Set α} :
    (∃ a, IsLUB s a) ↔ IsLUB s (sSup s) :=
  ⟨fun ⟨_, h⟩ ↦ h.isLUB_sSup, fun h ↦ ⟨_, h⟩⟩

@[to_dual] alias ⟨isLUB_sSup_of_exists, _⟩ := exists_isLUB_iff_isLUB_sSup

namespace Set

/-- Intersection of a set of sets. -/
def sInter (S : Set (Set α)) : Set α :=
  sInf S

/-- Notation for `Set.sInter` Intersection of a set of sets. -/
prefix:110 "⋂₀ " => sInter

/-- Union of a set of sets. -/
def sUnion (S : Set (Set α)) : Set α :=
  sSup S

/-- Notation for `Set.sUnion`. Union of a set of sets. -/
prefix:110 "⋃₀ " => sUnion

/-- Indexed union of a family of sets -/
def iUnion (s : ι → Set α) : Set α :=
  iSup s

/-- Indexed intersection of a family of sets -/
def iInter (s : ι → Set α) : Set α :=
  iInf s

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

@[simp]
theorem sSup_eq_sUnion (S : Set (Set α)) : sSup S = ⋃₀ S :=
  rfl

@[simp]
theorem sInf_eq_sInter (S : Set (Set α)) : sInf S = ⋂₀ S :=
  rfl

@[simp]
theorem iSup_eq_iUnion (s : ι → Set α) : iSup s = iUnion s :=
  rfl

@[simp]
theorem iInf_eq_iInter (s : ι → Set α) : iInf s = iInter s :=
  rfl

end Set
