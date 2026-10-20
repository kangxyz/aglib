/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Affine.Coordinates
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.VariableChange
public import Aglib.RingTheory.AdjoinRoot.BivariateTensor
public import Mathlib.RingTheory.RingHom.Etale

/-!
# Translation and coefficient transport on the actual affine coordinate ring

Translation delegates to the generic admissible-variable-change maps at scale
one and shear zero. The displayed coordinate formulas identify the original
forward and inverse maps on Mathlib's literal coordinate ring.
Source: affine part of
`R5Lab.AlgebraicGeometry.Curves.LocalModels.PointedResolution.Nodal.CoordinateTransport`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`1653a07650513593b903cc7b5db4793870399c969bebf70aa4ca0c159c759984`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
open scoped Polynomial.Bivariate TensorProduct
universe u
namespace WeierstrassCurve
variable {R : Type u} [CommRing R]

/-- The original forward translation map, as the generic admissible substitution. -/
def affineTranslateHom (W : WeierstrassCurve R) (r t : R) :
    W.toAffine.CoordinateRing →ₐ[R] (translate W r t).toAffine.CoordinateRing :=
  VariableChange.affineMap W (.mk 1 r 0 t)

@[simp] theorem affineTranslateHom_x (W : WeierstrassCurve R) (r t : R) :
    affineTranslateHom W r t (affineX W) =
      affineX (translate W r t) + algebraMap R _ r := by
  dsimp only [affineTranslateHom, translate]
  rw [VariableChange.affineMap_x]
  simp [VariableChange.changeX, VariableChange.map]

@[simp] theorem affineTranslateHom_y (W : WeierstrassCurve R) (r t : R) :
    affineTranslateHom W r t (affineY W) =
      affineY (translate W r t) + algebraMap R _ t := by
  dsimp only [affineTranslateHom, translate]
  rw [VariableChange.affineMap_y]
  simp [VariableChange.changeY, VariableChange.map]

/-- The original inverse translation map, on the same actual coordinate rings. -/
def affineUntranslateHom (W : WeierstrassCurve R) (r t : R) :
    (translate W r t).toAffine.CoordinateRing →ₐ[R] W.toAffine.CoordinateRing :=
  VariableChange.affineInverse W (.mk 1 r 0 t)

@[simp] theorem affineUntranslateHom_x (W : WeierstrassCurve R) (r t : R) :
    affineUntranslateHom W r t (affineX (translate W r t)) =
      affineX W - algebraMap R _ r := by
  dsimp only [affineUntranslateHom, translate]
  rw [VariableChange.affineInverse_x]
  simp [VariableChange.changeX, VariableChange.map, VariableChange.inv_def, sub_eq_add_neg]

@[simp] theorem affineUntranslateHom_y (W : WeierstrassCurve R) (r t : R) :
    affineUntranslateHom W r t (affineY (translate W r t)) =
      affineY W - algebraMap R _ t := by
  dsimp only [affineUntranslateHom, translate]
  rw [VariableChange.affineInverse_y]
  simp [VariableChange.changeY, VariableChange.map, VariableChange.inv_def, sub_eq_add_neg]

/-- The actual coordinate-ring equivalence of the scale-one translation. -/
def affineTranslateEquiv (W : WeierstrassCurve R) (r t : R) :
    W.toAffine.CoordinateRing ≃ₐ[R] (translate W r t).toAffine.CoordinateRing :=
  VariableChange.affineEquiv W (.mk 1 r 0 t)

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The algebra equivalence identifying the scalar extension of an affine Weierstrass coordinate
ring with the coordinate ring of the curve with extended coefficients. -/
def affineTensorEquiv (W : WeierstrassCurve R) :
    S ⊗[R] W.toAffine.CoordinateRing ≃ₐ[S] (W.map (algebraMap R S)).toAffine.CoordinateRing :=
  AdjoinRoot.bivariateTensorEquiv W.toAffine.polynomial
    (W.map (algebraMap R S)).toAffine.polynomial (by
      simp [WeierstrassCurve.Affine.polynomial, WeierstrassCurve.map])

/-- The actual map from the original affine coordinate ring under coefficient extension. -/
def affineCoefficientMap (W : WeierstrassCurve R) :
    W.toAffine.CoordinateRing →ₐ[R] (W.map (algebraMap R S)).toAffine.CoordinateRing :=
  ((affineTensorEquiv S W).toAlgHom.restrictScalars R).comp
    Algebra.TensorProduct.includeRight

@[simp] theorem affineCoefficientMap_x (W : WeierstrassCurve R) :
    affineCoefficientMap S W (affineX W) = affineX (W.map (algebraMap R S)) := by
  change (affineTensorEquiv S W) (1 ⊗ₜ[R] affineX W) = _
  unfold affineTensorEquiv AdjoinRoot.bivariateTensorEquiv
  rw [AlgEquiv.trans_apply]
  rw [show affineX W = AdjoinRoot.of _ X from rfl, AdjoinRoot.tensorAlgEquiv_of]
  rw [AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_of]
  simp [affineX, AdjoinRoot.algebraMap_eq]


@[simp] theorem affineCoefficientMap_y (W : WeierstrassCurve R) :
    affineCoefficientMap S W (affineY W) = affineY (W.map (algebraMap R S)) := by
  change (affineTensorEquiv S W) (1 ⊗ₜ[R] affineY W) = _
  unfold affineTensorEquiv AdjoinRoot.bivariateTensorEquiv
  rw [AlgEquiv.trans_apply]
  rw [AdjoinRoot.tensorAlgEquiv_root]
  rw [AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_root]


/-- Coefficient extension is genuinely etale on the original affine scheme. -/
theorem affineCoefficientMap_etale [Algebra.Etale R S] (W : WeierstrassCurve R) :
    (affineCoefficientMap S W).toRingHom.Etale := by
  let e := Algebra.TensorProduct.comm R S (W.toAffine.CoordinateRing)
  have hi : (Algebra.TensorProduct.includeRight :
      W.toAffine.CoordinateRing →ₐ[R] S ⊗[R] W.toAffine.CoordinateRing).toRingHom.Etale := by
    have hl : (algebraMap (W.toAffine.CoordinateRing) (W.toAffine.CoordinateRing ⊗[R] S)).Etale :=
      RingHom.etale_algebraMap.mpr inferInstance
    have hh := RingHom.Etale.stableUnderComposition _ _ hl
      (RingHom.Etale.of_bijective (f := e.symm.toRingHom) e.symm.bijective)
    exact hh
  exact RingHom.Etale.stableUnderComposition _ _ hi
    (RingHom.Etale.of_bijective (f := (affineTensorEquiv S W).toRingHom)
      (affineTensorEquiv S W).bijective)


end WeierstrassCurve
