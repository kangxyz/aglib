/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.SmoothLoci
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.BaseChange

/-! Actual gradient support, chart smoothness, and original coefficient/infinity triangles. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
namespace WeierstrassSmoothLociTest

open WeierstrassCurve.Projective

example {R : Type u} [CommRing R] (W : WeierstrassCurve R) (i : Fin 2) :
    SmoothOfRelativeDimension 1 (affineSmoothChart W i ≫ structureMap W) := inferInstance

example {R : Type u} [CommRing R] (W : WeierstrassCurve R) (p : scheme W) :
    p ∈ (affineChart W).opensRange ∨ p ∈ (infinitySmoothChart W).opensRange :=
  affine_or_smoothInfinity W p

example {k : Type u} [Field k] (W : WeierstrassCurve k) (r s : k)
    (he : W.toAffine.Equation r s) :
    affineSingularPoint W r s he =
      (affinePointOver W r s he).left (IsLocalRing.closedPoint k) := rfl

example {k : Type u} [Field k] (W : WeierstrassCurve k) (r s : k)
    (he : W.toAffine.Equation r s)
    (hx : W.toAffine.polynomialX.evalEval r s = 0)
    (hy : W.toAffine.polynomialY.evalEval r s = 0)
    (p : PrimeSpectrum (affineRing W)) :
    (affineChart W p ∈ (affineSmoothChart W 0).opensRange ∨
      affineChart W p ∈ (affineSmoothChart W 1).opensRange) ↔
      p ≠ affineSingularPoint W r s he := by
  have h0 : affineChart W p ∈ (affineSmoothChart W 0).opensRange ↔
      affineGradientX W ∉ p.asIdeal :=
    (affineChart_mem_smoothChart_iff W 0 p).trans (by rw [affineJacobian_zero]; rfl)
  have h1 : affineChart W p ∈ (affineSmoothChart W 1).opensRange ↔
      affineGradientY W ∉ p.asIdeal :=
    (affineChart_mem_smoothChart_iff W 1 p).trans (by rw [affineJacobian_one]; rfl)
  exact (or_congr h0 h1).trans (not_and_or.symm.trans
    (not_congr (affine_singular_point_iff W r s he hx hy p)).symm)

example {R S : Type u} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (f : R →+* S) :
    infinitySmoothSection (W.map f) ≫ infinitySmoothChart (W.map f) ≫
      coefficientSchemeMap W f = Spec.map (CommRingCat.ofHom f) ≫ infinitySection W := by
  rw [← Category.assoc, infinitySmoothSection_chart, infinitySection_coefficient]

end WeierstrassSmoothLociTest
