/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Affine.CoordinateTransport
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.VariableChangeChart
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.Points
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.CriticalCubic.AffineNormalization
public import Aglib.AlgebraicGeometry.Curves.Nodal.CriticalPoint

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.SingularCubic`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`bfe1575f218bd9a0e8a5247871f4ef3057201e92a5b4625f4953d8059f6b6a86`.
Only the field-level source586–750. Existing
  affineTranslateHom/affineUntranslateHom/affineTranslateEquiv and the actual
  VariableChange.affineSpecIso are reused, with the original forward x↦x+r, y↦y+s map. No
  duplicated substitution or projective translation is defined.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open AlgebraicGeometry.Scheme WeierstrassCurve

section WeierstrassCurve.CriticalCubic.SingularTranslation


/-! Exact field-level translation of the actual rational singular point to
the origin, with actual affine coordinate-ring maps. No splitness is assumed. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
namespace WeierstrassCurve.CriticalCubic.SingularTranslation
open WeierstrassCurve.Projective WeierstrassCurve.CriticalPoint
universe u
variable {k : Type u} [Field k]

/-- Literal equality of the translated equation with the same critical cubic
used by its explicit normalization. The orientation is old(x,y)=new(x+r,y+s). -/
theorem translate_eq_critical (W : WeierstrassCurve k) (r s : k)
    (he : W.toAffine.Equation r s)
    (hx : W.toAffine.polynomialX.evalEval r s = 0)
    (hy : W.toAffine.polynomialY.evalEval r s = 0) :
    translate W r s = WeierstrassCurve.CriticalCubic.equation k W.a₁ (W.a₂ + 3 * r) := by
  obtain ⟨h3, h4⟩ := (translate_critical_iff W r s).mpr ⟨hx, hy⟩
  have h6 : (translate W r s).a₆ = 0 := by
    rw [translate_a6, show W.toAffine.polynomial.evalEval r s = 0 from he, neg_zero]
  ext <;> simp only [translate_a1, translate_a2, WeierstrassCurve.CriticalCubic.equation, h3, h4,
    h6]

/-- The exact translated affine chart, oriented towards the original chart. -/
def translatedAffineIso (W : WeierstrassCurve k) (r s : k) :
    Spec (.of (affineRing (translate W r s))) ≅ Spec (.of (affineRing W)) :=
  WeierstrassCurve.VariableChange.affineSpecIso W (.mk 1 r 0 s)

@[simp] theorem translatedAffineIso_hom (W : WeierstrassCurve k) (r s : k) :
    (translatedAffineIso W r s).hom = Spec.map (CommRingCat.ofHom
      (WeierstrassCurve.affineTranslateHom W r s).toRingHom) := rfl

@[reassoc] theorem translatedAffineIso_structure (W : WeierstrassCurve k) (r s : k) :
    (translatedAffineIso W r s).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (affineRing W))) =
        Spec.map (CommRingCat.ofHom (algebraMap k (affineRing (translate W r s)))) := by
  rw [translatedAffineIso_hom, ← Spec.map_comp]
  congr 1
  ext a
  exact (WeierstrassCurve.affineTranslateHom W r s).commutes a

/-- Actual equation membership is transported by the exact coordinate substitution. -/
theorem translatedEquation_iff (W : WeierstrassCurve k) (r s x y : k) :
    (translate W r s).toAffine.Equation x y ↔ W.toAffine.Equation (x + r) (y + s) := by
  change (translate W r s).toAffine.polynomial.evalEval x y = 0 ↔ _
  rw [translate_polynomial_eval]
  rfl

/-- The actual affine point-map triangle, including the singular point. -/
theorem translatedAffineIso_point (W : WeierstrassCurve k) (r s x y : k)
    (he : (translate W r s).toAffine.Equation x y) :
    (affinePointOver _ x y he).left ≫ (translatedAffineIso W r s).hom =
      (affinePointOver W (x + r) (y + s) ((translatedEquation_iff W r s x y).mp he)).left := by
  rw [translatedAffineIso_hom]
  change Spec.map (CommRingCat.ofHom (affinePointEval _ x y he)) ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply affinePointEval_ext
  · intro a
    change affinePointEval _ x y he (WeierstrassCurve.affineTranslateHom W r s (algebraMap k _ a)) =
      affinePointEval W (x + r) (y + s) ((translatedEquation_iff W r s x y).mp he) (algebraMap k _
        a)
    rw [AlgHom.commutes, affinePointEval_constant, affinePointEval_constant]
  · change affinePointEval _ x y he (WeierstrassCurve.affineTranslateHom W r s (affineX W)) =
      affinePointEval W (x + r) (y + s) ((translatedEquation_iff W r s x y).mp he) (affineX W)
    simp only [WeierstrassCurve.affineTranslateHom_x, map_add, affinePointEval_x,
      affinePointEval_constant]
  · change affinePointEval _ x y he (WeierstrassCurve.affineTranslateHom W r s (affineY W)) =
      affinePointEval W (x + r) (y + s) ((translatedEquation_iff W r s x y).mp he) (affineY W)
    simp only [WeierstrassCurve.affineTranslateHom_y, map_add, affinePointEval_y,
      affinePointEval_constant]

/-- The translated affine origin is an actual point precisely because the
original coordinates lie on the literal original equation. -/
theorem translatedOriginEquation (W : WeierstrassCurve k) (r s : k)
    (he : W.toAffine.Equation r s) : (translate W r s).toAffine.Equation 0 0 :=
  (translatedEquation_iff W r s 0 0).mpr (by simpa only [zero_add] using he)

/-- Actual translated affine origin to actual original rational point. -/
theorem translatedAffineIso_origin (W : WeierstrassCurve k) (r s : k)
    (he : W.toAffine.Equation r s) :
    (affinePointOver _ 0 0 (translatedOriginEquation W r s he)).left ≫
      (translatedAffineIso W r s).hom = (affinePointOver W r s he).left := by
  simpa only [zero_add] using translatedAffineIso_point W r s 0 0 (translatedOriginEquation W r s
    he)

/-- The point-map triangle lands in the actual original projective equation,
through its actual affine chart. This does not assert a global projective
translation isomorphism. -/
@[reassoc] theorem translatedOrigin_projective (W : WeierstrassCurve k) (r s : k)
    (he : W.toAffine.Equation r s) :
    (affinePointOver _ 0 0 (translatedOriginEquation W r s he)).left ≫
      (translatedAffineIso W r s).hom ≫ affineChart W =
        (affinePointOver W r s he).left ≫ affineChart W := by
  rw [← Category.assoc, translatedAffineIso_origin]


end WeierstrassCurve.CriticalCubic.SingularTranslation
end
end WeierstrassCurve.CriticalCubic.SingularTranslation
