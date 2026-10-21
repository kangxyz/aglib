/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.AffineChart

/-!
Native extraction from the R5 local-model source
`PointedResolution.Weierstrass.DVRNode`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`fe38de93b452fcb595b6def1a29f64a03b8ab2e6827928324d02c4b31c6b7fb1`.
Exact local residue-evaluation and actual projective residue-point slices72–96 and190–245.
  Existing CoordinateRing, projective scheme and affineChart are reused.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry IsLocalRing Polynomial
open WeierstrassCurve
universe u

namespace WeierstrassCurve.Projective
variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Evaluation of the affine coordinate ring at the residue-field solution `(r, s)`,
with coefficients reduced by the residue map of `R`. -/
def affineResidueEval (W : WeierstrassCurve R) (r s : ResidueField R)
    (he : (W.map (residue R)).toAffine.Equation r s) : W.toAffine.CoordinateRing →+* ResidueField
      R :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (residue R) r) s (by
    simp only [WeierstrassCurve.Affine.polynomial, Polynomial.eval₂_add,
      Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.coe_eval₂RingHom]
    convert (WeierstrassCurve.Affine.equation_iff' _ _).mp he using 1
    simp [WeierstrassCurve.map]
    ring)

@[simp] lemma affineResidueEval_x (W : WeierstrassCurve R) (r s : ResidueField R)
    (he : (W.map (residue R)).toAffine.Equation r s) :
    affineResidueEval W r s he (affineX W) = r := by
  simp [affineResidueEval, affineX, AdjoinRoot.lift_of]
@[simp] lemma affineResidueEval_y (W : WeierstrassCurve R) (r s : ResidueField R)
    (he : (W.map (residue R)).toAffine.Equation r s) :
    affineResidueEval W r s he (affineY W) = s := by
  simp [affineResidueEval, affineY, AdjoinRoot.lift_root]
@[simp] lemma affineResidueEval_constant (W : WeierstrassCurve R) (r s : ResidueField R)
    (he : (W.map (residue R)).toAffine.Equation r s) (a : R) :
    affineResidueEval W r s he (algebraMap R (W.toAffine.CoordinateRing) a) = residue R a := by
  change affineResidueEval W r s he (AdjoinRoot.of _ (Polynomial.C a)) = _
  simp [affineResidueEval, AdjoinRoot.lift_of]


/-- The point of the affine Weierstrass scheme defined by evaluation at the
residue-field solution `(r, s)`. -/
def affineResidueNode (W : WeierstrassCurve R) (r s : ResidueField R)
    (he : (W.map (residue R)).toAffine.Equation r s) : Spec (.of (W.toAffine.CoordinateRing)) :=
  Spec.map (CommRingCat.ofHom (affineResidueEval W r s he)) (closedPoint (ResidueField R))

lemma affineResidueNode_asIdeal (W : WeierstrassCurve R) (r s : ResidueField R)
    (he : (W.map (residue R)).toAffine.Equation r s) :
    (affineResidueNode W r s he).asIdeal = RingHom.ker (affineResidueEval W r s he) := by
  change Ideal.comap (affineResidueEval W r s he) (maximalIdeal (ResidueField R)) = _
  rw [maximalIdeal_eq_bot]
  rfl

/-- The morphism from the residue-field spectrum to the projective Weierstrass scheme
obtained by evaluating at `(r, s)` and then using the affine chart. -/
def residueNodeMap (W : WeierstrassCurve R) (r s : ResidueField R)
    (he : (W.map (residue R)).toAffine.Equation r s) : Spec (.of (ResidueField R)) ⟶ scheme W :=
  Spec.map (CommRingCat.ofHom (affineResidueEval W r s he)) ≫ affineChart W

@[reassoc] lemma residueNodeMap_structure (W : WeierstrassCurve R) (r s : ResidueField R)
    (he : (W.map (residue R)).toAffine.Equation r s) :
    residueNodeMap W r s he ≫ structureMap W = Spec.map (CommRingCat.ofHom (residue R)) := by
  rw [residueNodeMap, Category.assoc, affineChart_structure, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact affineResidueEval_constant W r s he

instance residueNodeMap_closedImmersion (W : WeierstrassCurve R) (r s : ResidueField R)
    (he : (W.map (residue R)).toAffine.Equation r s) : IsClosedImmersion (residueNodeMap W r s he)
      := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (residue R))) :=
    IsClosedImmersion.spec_of_surjective _ residue_surjective
  have : IsClosedImmersion (residueNodeMap W r s he ≫ structureMap W) := by
    rw [residueNodeMap_structure]
    infer_instance
  exact IsClosedImmersion.of_comp _ (structureMap W)

/-- The actual selected residue singular point in the original total scheme. -/
def residueNode (W : WeierstrassCurve R) (r s : ResidueField R)
    (he : (W.map (residue R)).toAffine.Equation r s) : scheme W :=
  residueNodeMap W r s he (closedPoint (ResidueField R))

lemma residueNode_eq_affine (W : WeierstrassCurve R) (r s : ResidueField R)
    (he : (W.map (residue R)).toAffine.Equation r s) :
    residueNode W r s he = affineChart W (affineResidueNode W r s he) := rfl

lemma residueNode_isClosed (W : WeierstrassCurve R) (r s : ResidueField R)
    (he : (W.map (residue R)).toAffine.Equation r s) :
    IsClosed ({residueNode W r s he} : Set (scheme W)) := by
  simpa only [Set.image_singleton, residueNode] using
    (residueNodeMap W r s he).isClosedMap {closedPoint (ResidueField R)} isClosed_singleton

/-- The genuine open complement of the specified actual residue point. -/
def residueNodeComplement (W : WeierstrassCurve R) (r s : ResidueField R)
    (he : (W.map (residue R)).toAffine.Equation r s) : (scheme W).Opens :=
  ⟨{residueNode W r s he}ᶜ, (residueNode_isClosed W r s he).isOpen_compl⟩

@[simp] lemma mem_residueNodeComplement (W : WeierstrassCurve R) (r s : ResidueField R)
    (he : (W.map (residue R)).toAffine.Equation r s) (p : scheme W) :
    p ∈ residueNodeComplement W r s he ↔ p ≠ residueNode W r s he := Iff.rfl

end WeierstrassCurve.Projective
