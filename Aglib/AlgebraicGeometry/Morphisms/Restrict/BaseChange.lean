/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-! # Original open restrictions in a cartesian square

A base-change-stable property of the original open restriction holds on its
literal inverse-open restriction. The proof uses the native restricted square.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Base change retains a property on the original target-open restriction,
without replacing either source by a chosen pullback scheme. -/
theorem property_morphismRestrict_of_isPullback
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {Y' Y X' X : Scheme.{u}} {a : Y' ⟶ Y} {f' : Y' ⟶ X'}
    {f : Y ⟶ X} {b : X' ⟶ X} (H : IsPullback a f' f b)
    (U : X.Opens) (hP : P (f ∣_ U)) : P (f' ∣_ (b ⁻¹ᵁ U)) := by
  have he : a ⁻¹ᵁ (f ⁻¹ᵁ U) = f' ⁻¹ᵁ (b ⁻¹ᵁ U) := by
    rw [← comp_preimage, H.w, comp_preimage]
  have H' := Scheme.Hom.isPullback_resLE H
    (US := U) (UT := b ⁻¹ᵁ U) (UX := f ⁻¹ᵁ U)
    (UY := f' ⁻¹ᵁ (b ⁻¹ᵁ U)) le_rfl le_rfl (by simp only [he, inf_idem])
  have hf : P (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
    rw [resLE_eq_morphismRestrict]
    exact hP
  have hp := MorphismProperty.of_isPullback H' hf
  simpa only [resLE_eq_morphismRestrict] using hp

end AlgebraicGeometry.Scheme.Hom
