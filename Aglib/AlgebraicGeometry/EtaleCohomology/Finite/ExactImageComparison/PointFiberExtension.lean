/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Over.FixedFiberHom

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.GeometricPointExtension

/-! # Original geometric Hom fibres under a separably closed field extension -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits



namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

variable {κ Ω : Type u} [Field κ] [IsSepClosed κ] [Field Ω]
  {X : Scheme.{u}} (ξ : Spec (.of κ) ⟶ X) (e : Spec (.of Ω) ⟶ Spec (.of κ))

/-- The original map on actual geometric Hom fibres is precomposition by the field map. -/
def pointFiberExtension (U : X.Etale) :
    (Over.mk ξ ⟶ (Scheme.Etale.forget X).obj U) →
      (Over.mk (e ≫ ξ) ⟶ (Scheme.Etale.forget X).obj U) :=
  fun p => (Over.homMk e rfl : Over.mk (e ≫ ξ) ⟶ Over.mk ξ) ≫ p

/-- Actual geometric Hom fibres are unchanged by extension of the separably closed field. -/
theorem pointFiberExtension_bijective (U : X.Etale) :
    Function.Bijective (pointFiberExtension ξ e U) := by
  have : Etale U.hom := U.prop
  exact bijective_over_precomp_of_pullback U.hom ξ e
    (bijective_etale_point_extension e (pullback.snd U.hom ξ))

end AlgebraicGeometry.Scheme.EtaleCohomology
