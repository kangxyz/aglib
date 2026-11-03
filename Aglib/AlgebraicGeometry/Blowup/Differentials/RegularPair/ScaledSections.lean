/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Differentials.RegularPair.SheafBound
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.AffineLineKernel
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.LinearAlgebra.LinearMap.ScaledImageLift
public import Aglib.RingTheory.Localization.Away.SaturatedChart.FractionRing


/-!
# The actual regular-pair scaled coefficient on sections

The original raw image bound and original line-valued kernel containment
construct the scaled map. The SAME original fraction field is proved to be
the actual chart's fraction field. The exceptional coordinate and original
coefficient normalization are retained exactly.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u vK


open AlgebraicGeometry.Scheme.Modules.Differentials
open LinearMap
open Localization.Away

namespace AlgebraicGeometry.Scheme.Blowup.RegularPair

variable (Λ R : Type u) (K : Type vK) [CommRing Λ] [CommRing R] [IsDomain R] [Field K]
  [Algebra Λ R] [Algebra R K] [Algebra Λ K] [IsScalarTower Λ R K]
  [IsFractionRing R K] (x y : R)
  (hx : IsSMulRegular R x) (hy : IsSMulRegular (R ⧸ Ideal.span {x}) y)
  (n : ℕ) (L : Invertible.LineBundle (Spec (.of R)))
  (φ : moduleExteriorPower (Spec (.of R))
    (relativeDifferentialSheaf (Spec.map (CommRingCat.ofHom (algebraMap Λ R)))) n ⟶ L.val)

local notation "S" =>
  Localization.Away.saturatedChart R (Ideal.span (Set.insert x (Set.singleton y))) x
local notation "α" => CommRingCat.ofHom (algebraMap Λ R)
local notation "σ" => CommRingCat.ofHom (algebraMap R S)

/-- The actual scaled inverse for the original raw pullback and original
coefficient into the actual pulled-back line. No image/kernel premise is supplied. -/
def saturatedPairScaledSections :
    moduleSpecΓFunctor.obj (moduleExteriorPower (Spec (.of S))
      (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n) →ₗ[S]
    moduleSpecΓFunctor.obj ((pullback (Spec.map σ)).obj L.val) := by
  have hx0 : x ≠ 0 := by
    intro h
    exact one_ne_zero (hx (by simp [h]))
  letI := Localization.Away.saturatedChartFractionAlgebra R K (Ideal.span {x, y}) x hx0
  letI := Localization.Away.saturatedChartFractionAlgebra_tower R K (Ideal.span {x, y}) x hx0
  letI := Localization.Away.saturatedChart_isFractionRing R K (Ideal.span {x, y}) x hx0
  letI : IsScalarTower Λ S K := IsScalarTower.to₁₃₄ Λ R S K
  exact LinearMap.scaledImageLift
    (moduleSpecΓFunctor.map (rawFormsPullback (Spec.map α) (Spec.map σ) n)).hom
    (moduleSpecΓFunctor.map ((pullback (Spec.map σ)).map φ)).hom (algebraMap R S x)
    (saturatedPair_rawPullback_imageBound α x y hx hy n)
    (rawPullback_ker_le_lineCoefficient Λ R S K n L φ)

/-- The constructed map has exactly the original exceptional-coordinate
normalization on the original raw coefficient, not an unspecified scalar. -/
theorem saturatedPairScaledSections_comp
    (p : moduleSpecΓFunctor.obj ((pullback (Spec.map σ)).obj
      (moduleExteriorPower (Spec (.of R)) (relativeDifferentialSheaf (Spec.map α)) n))) :
    saturatedPairScaledSections Λ R K x y hx hy n L φ
      (moduleSpecΓFunctor.map (rawFormsPullback (Spec.map α) (Spec.map σ) n) p) =
    algebraMap R S x • (moduleSpecΓFunctor.map ((pullback (Spec.map σ)).map φ) p) := by
  unfold saturatedPairScaledSections
  exact LinearMap.scaledImageLift_comp_apply _ _ _ _ _ p

end AlgebraicGeometry.Scheme.Blowup.RegularPair
