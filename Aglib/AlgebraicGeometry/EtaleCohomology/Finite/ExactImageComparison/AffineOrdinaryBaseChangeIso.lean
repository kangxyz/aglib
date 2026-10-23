/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.AffineOrdinaryBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.StalkUniverse

/-! # The original finite ordinary exchange over affine bases -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u

attribute [local instance] hasSheafifyLarge

variable (R R' : Type u) [CommRing R] [CommRing R']
  {X X' : Scheme.{u}} (f : X ⟶ Spec (.of R)) (f' : X' ⟶ Spec (.of R'))
  [IsFinite f] [IsFinite f'] (g : Spec (.of R') ⟶ Spec (.of R)) (g' : X' ⟶ X)
  (h : IsPullback g' f' f g)

/-- Finite ordinary base change with affine bases, for the original canonical
mate and arbitrary abelian coefficients. No noetherian hypothesis is used. -/
theorem finiteAffineBaseChange_app_isIso (F : AbelianSheaf.{u, u + 1} X) :
    IsIso ((baseChangeMap f f' g g' h.w.symm).app F) := by
  apply StalkUniverse.isIso_of_all_original_fibrewiseClosed_geometricStalks
    (𝟙 (Spec (.of R')))
  intro Ω _ _ ξ _
  let : Algebra R' Ω := (Spec.preimage ξ).hom.toAlgebra
  let : Algebra R Ω := (Spec.preimage (ξ ≫ g)).hom.toAlgebra
  have hξ : Spec.algebraMap R' Ω = ξ := by
    change Spec.map (Spec.preimage ξ) = ξ
    exact Spec.map_preimage ξ
  have hξg : Spec.algebraMap R Ω = ξ ≫ g := by
    change Spec.map (Spec.preimage (ξ ≫ g)) = ξ ≫ g
    exact Spec.map_preimage (ξ ≫ g)
  have hp : Spec.algebraMap R' Ω ≫ g = Spec.algebraMap R Ω := by
    rw [hξ, hξg]
  have hi := finiteAffineBaseChange_stalk_isIso R R' Ω f f' g g' h hp F
  rw [hξ] at hi
  exact hi

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
