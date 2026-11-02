/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.Derived
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenFullyFaithful

/-!
# Vanishing of closed restriction of the original derived open extension

The original localization triangle, full faithfulness of open extension, and
the triangle identity of the closed inverse/direct-image adjunction give the
vanishing on the complementary closed subscheme. No proper base change or
faithfulness of the closed direct image is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wU wZ wX

variable {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (Λ : Type (u + 1)) [Ring Λ] (i : Z ⟶ X) [IsClosedImmersion i]
  (hcomp : Set.range j = (Set.range i)ᶜ)
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

include hcomp

/-- Derived extension by zero restricts to zero on the complementary closed subscheme. -/
theorem isZero_moduleDerivedInverseImage_lowerShriek
    (M : DerivedCategory.Plus (ModuleSheaf U Λ)) :
    IsZero ((moduleDerivedInverseImage Λ i).obj ((moduleDerivedLowerShriek j Λ).obj M)) := by
  let K := (moduleDerivedLowerShriek j Λ).obj M
  let adj := moduleDerivedAdjunction Λ i
  have hε : IsIso ((moduleDerivedLowerShriekAdjunction j Λ).counit.app K) :=
    (moduleDerivedLowerShriekAdjunction j Λ).isIso_counit_app_of_iso (Iso.refl _)
  have hz : IsZero ((moduleDerivedDirectImage Λ i).obj
      ((moduleDerivedInverseImage Λ i).obj K)) :=
    (moduleDerivedLocalizationTriangle j Λ i hcomp K).isZero₃_of_isIso₁
      (moduleDerivedLocalizationTriangle_distinguished j Λ i hcomp K) hε
  have hη : adj.unit.app K = 0 := hz.eq_zero_of_tgt _
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← adj.left_triangle_components K, hη, Functor.map_zero, zero_comp]

end AlgebraicGeometry.Scheme.EtaleCohomology
