/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.MonoFactor
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Blowup.CommonCenters
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.ResidueNode

/-!
Native extraction from the R5 local-model source
`PointedResolution.Blowup.ProjectiveCenter`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`a3623d73d63d310291e8c4af9558b1b7d66700e7681a5c31889865c2f4ff34de`.
Original objects, maps, quantifiers and mathematical hypotheses are retained.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode

/-!
# The actual projective Weierstrass node centre and its pullback to the common pointed étale chart.

The declarations retain their original qualified interfaces and mathematical
inputs; the source-coverage comments below retain their original boundaries.
-/

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme WeierstrassCurve
universe u

section ProjectiveNodeCenter


/-! Exact pullback of the actual projective residue-point centre along the
original affine open chart and then the same common etale chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open WeierstrassCurve.CriticalNeighborhood
namespace AlgebraicGeometry.Scheme.PowerNode.ProjectiveNodeBlowup
open AlgebraicGeometry.Scheme.PowerNode.CommonChartBlowup


open WeierstrassCurve.Projective
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}

/-- The two accepted affine evaluations are the same actual ring map. -/
lemma affineResidueEval_eq_originalResidue
    (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y) :
    affineResidueEval W x y he = (WeierstrassCurve.CriticalNeighborhood.originalResidue
      he).toRingHom := by
  let f : W.toAffine.CoordinateRing →ₐ[R] ResidueField R :=
    { affineResidueEval W x y he with
      commutes' := fun r => by
        change affineResidueEval W x y he (AdjoinRoot.of _ (Polynomial.C r)) =
          IsLocalRing.residue R r
        simp [affineResidueEval, AdjoinRoot.lift_of] }
  have h : f = WeierstrassCurve.CriticalNeighborhood.originalResidue he := by
    apply WeierstrassCurve.affine_ext
    · change affineResidueEval W x y he (affineX W) = _
      simp [WeierstrassCurve.CriticalNeighborhood.originalResidue]
    · change affineResidueEval W x y he (affineY W) = _
      simp [WeierstrassCurve.CriticalNeighborhood.originalResidue]
  exact congrArg AlgHom.toRingHom h

lemma residueNodeMap_eq_original
    (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y) :
    residueNodeMap W x y he =
      Spec.map (CommRingCat.ofHom (WeierstrassCurve.CriticalNeighborhood.originalResidue
        he).toRingHom) ≫
        affineChart W := by
  rw [residueNodeMap, affineResidueEval_eq_originalResidue he]

/-- The global centre is exactly the kernel of the given original residue point. -/
def projectiveCenter (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y) :
    (scheme W).IdealSheafData := (residueNodeMap W x y he).ker

variable (M : WeierstrassCurve.CriticalNeighborhood W x y)

lemma affine_center_comap (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y) :
    (projectiveCenter he).comap (affineChart W) =
      AlgebraicGeometry.Scheme.PowerNode.CommonChartBlowup.originalCenterSheaf M := by
  let : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (WeierstrassCurve.CriticalNeighborhood.originalResidue
        he).toRingHom) ≫
        affineChart W) := by
    rw [← residueNodeMap_eq_original he]
    infer_instance
  rw [projectiveCenter, residueNodeMap_eq_original he,
    AlgebraicGeometry.Scheme.PowerNode.CommonChartBlowup.originalCenterSheaf_eq_point_kernel M he]
  exact Scheme.IdealSheafData.ker_comap_of_mono _ _

/-- The original common chart maps to the same original projective equation. -/
def commonToProjective : M.commonScheme ⟶ scheme W :=
  M.toOriginalScheme ≫ affineChart W

instance commonToProjective_etale : Etale (commonToProjective M) := by
  dsimp [commonToProjective]
  infer_instance

/-- The common centre is the full inverse image of the original projective
residue-point ideal. It need not be the ideal of one chosen common-chart point. -/
lemma common_center_comap (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y) :
    (projectiveCenter he).comap (commonToProjective M) =
      AlgebraicGeometry.Scheme.PowerNode.CommonChartBlowup.commonCenterSheaf M := by
  rw [commonToProjective, Scheme.IdealSheafData.comap_comp, affine_center_comap M he]
  rfl

end AlgebraicGeometry.Scheme.PowerNode.ProjectiveNodeBlowup

end
end ProjectiveNodeCenter
