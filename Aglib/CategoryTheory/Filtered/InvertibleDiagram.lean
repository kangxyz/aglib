/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Functor.Category

/-!
# Canonical comparisons in invertible cofiltered diagrams

A contravariant diagram on a cofiltered category which sends every arrow to an
isomorphism has canonical comparisons between any two values. The comparison
can be computed using any common predecessor. Equalization of parallel arrows
makes this formula independent of choices, and gives its identity and cocycle
laws. No limits, colimits, small skeleton, or special target category are used.
-/

@[expose] public noncomputable section

universe vJ vE uJ uE

namespace CategoryTheory.Functor

open Opposite IsIso

variable {J : Type uJ} [Category.{vJ} J] {E : Type uE} [Category.{vE} E]
  (F : Jᵒᵖ ⥤ E) [∀ (i j : Jᵒᵖ) (f : i ⟶ j), IsIso (F.map f)]

/-- The comparison represented by a common predecessor of two objects. -/
def cofilteredSpanIso {i j k : J} (a : i ⟶ j) (b : i ⟶ k) :
    F.obj (op j) ≅ F.obj (op k) :=
  asIso (F.map a.op) ≪≫ (asIso (F.map b.op)).symm

/-- Refining a common predecessor does not change its comparison. -/
theorem cofilteredSpanIso_comp {i i' j k : J} (r : i' ⟶ i)
    (a : i ⟶ j) (b : i ⟶ k) :
    F.cofilteredSpanIso (r ≫ a) (r ≫ b) = F.cofilteredSpanIso a b := by
  apply Iso.ext
  simp [cofilteredSpanIso, Functor.map_comp, inv_comp, Category.assoc]

variable [IsCofilteredOrEmpty J]

/-- An invertible contravariant cofiltered diagram identifies parallel arrows. -/
theorem map_eq_of_cofiltered {i j : J} (a b : i ⟶ j) :
    F.map a.op = F.map b.op := by
  apply (cancel_mono (F.map (IsCofiltered.eqHom a b).op)).mp
  simpa only [op_comp, Functor.map_comp] using
    congrArg (fun f => F.map f.op) (IsCofiltered.eq_condition a b)

/-- The common-predecessor formula is independent of both the predecessor and
its two arrows. -/
theorem cofilteredSpanIso_eq {i i' j k : J} (a : i ⟶ j) (b : i ⟶ k)
    (a' : i' ⟶ j) (b' : i' ⟶ k) :
    F.cofilteredSpanIso a b = F.cofilteredSpanIso a' b' := by
  let r := IsCofiltered.minToLeft i i'
  let s := IsCofiltered.minToRight i i'
  rw [← F.cofilteredSpanIso_comp r a b, ← F.cofilteredSpanIso_comp s a' b']
  have ha : asIso (F.map (r ≫ a).op) = asIso (F.map (s ≫ a').op) :=
    Iso.ext (F.map_eq_of_cofiltered (r ≫ a) (s ≫ a'))
  have hb : asIso (F.map (r ≫ b).op) = asIso (F.map (s ≫ b').op) :=
    Iso.ext (F.map_eq_of_cofiltered (r ≫ b) (s ≫ b'))
  exact congrArg₂ (fun α β => α ≪≫ β.symm) ha hb

/-- The canonical comparison between two values of an invertible contravariant
cofiltered diagram. -/
def cofilteredComparison (j k : J) : F.obj (op j) ≅ F.obj (op k) :=
  F.cofilteredSpanIso (IsCofiltered.minToLeft j k) (IsCofiltered.minToRight j k)

/-- Any common predecessor computes the canonical comparison. -/
theorem cofilteredComparison_eq_span {i j k : J} (a : i ⟶ j) (b : i ⟶ k) :
    F.cofilteredComparison j k = F.cofilteredSpanIso a b :=
  F.cofilteredSpanIso_eq _ _ a b

@[simp]
theorem cofilteredComparison_self (j : J) :
    F.cofilteredComparison j j = Iso.refl _ := by
  rw [F.cofilteredComparison_eq_span (𝟙 j) (𝟙 j)]
  apply Iso.ext
  simp [cofilteredSpanIso]

/-- The canonical comparisons satisfy the cocycle equation. -/
@[simp]
theorem cofilteredComparison_trans (j k l : J) :
    F.cofilteredComparison j k ≪≫ F.cofilteredComparison k l =
      F.cofilteredComparison j l := by
  let r := IsCofiltered.minToLeft (IsCofiltered.min j k) l
  let a := r ≫ IsCofiltered.minToLeft j k
  let b := r ≫ IsCofiltered.minToRight j k
  let c := IsCofiltered.minToRight (IsCofiltered.min j k) l
  rw [F.cofilteredComparison_eq_span a b, F.cofilteredComparison_eq_span b c,
    F.cofilteredComparison_eq_span a c]
  apply Iso.ext
  simp [cofilteredSpanIso]

/-- Along an original arrow, the canonical comparison is the inverse of the
original contravariant diagram map. -/
theorem cofilteredComparison_eq_inv_map {j k : J} (a : j ⟶ k) :
    F.cofilteredComparison j k = (asIso (F.map a.op)).symm := by
  rw [F.cofilteredComparison_eq_span (𝟙 j) a]
  apply Iso.ext
  simp [cofilteredSpanIso]

/-- Reversing the canonical comparison gives the opposite canonical comparison. -/
@[simp]
theorem cofilteredComparison_symm (j k : J) :
    (F.cofilteredComparison j k).symm = F.cofilteredComparison k j := by
  apply Iso.ext
  apply (cancel_epi (F.cofilteredComparison j k).hom).mp
  have h := congrArg Iso.hom (F.cofilteredComparison_trans j k j)
  rw [F.cofilteredComparison_self] at h
  simpa only [Iso.trans_hom, Iso.refl_hom, Iso.symm_hom, Iso.hom_inv_id] using h.symm

/-- Original diagram arrows are compatible with all canonical comparisons. -/
@[reassoc]
theorem cofilteredComparison_naturality {j j' k : J} (a : j' ⟶ j) :
    F.map a.op ≫ (F.cofilteredComparison j' k).hom =
      (F.cofilteredComparison j k).hom := by
  have h := congrArg Iso.hom (F.cofilteredComparison_trans j j' k)
  rw [← F.cofilteredComparison_symm j' j, F.cofilteredComparison_eq_inv_map a] at h
  simpa using h

end CategoryTheory.Functor
