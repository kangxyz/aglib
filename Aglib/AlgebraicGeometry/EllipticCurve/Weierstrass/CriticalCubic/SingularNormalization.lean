/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.CriticalCubic.TargetNormalization
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.CriticalCubic.SingularTranslation

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.BranchComparison`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`09bd3778c95ee312d11c130086332e1fbc7498f12b9e3bd82fa0fecc1c15830d`.
Only source378–483 needed by the strict/exceptional consumers: the actual critical chart,
  original-point triangle and same-equation normalization. The unconsumed source488+ branch
  reindexing theorem and all model/marked record assemblies remain downstream.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open AlgebraicGeometry.Scheme WeierstrassCurve

section SingularCubicBranchComparison


/-! Actual source-P1 reindexing for the literal translated singular cubic,
retaining both original-field endpoint sections and their distinct roots. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
namespace WeierstrassCurve.CriticalCubic.SingularNormalization
universe u
open WeierstrassCurve.Projective WeierstrassCurve.CriticalCubic.SingularTranslation
  WeierstrassCurve.CriticalPoint AlgebraicGeometry.Scheme.PinchedLine
variable {k : Type u} [Field k]
attribute [local instance] WeierstrassCurve.Projective.scheme_isIntegral_of_isDomain

lemma criticalOriginEquation (a b : k) : (WeierstrassCurve.CriticalCubic.equation k a
  b).toAffine.Equation 0 0 := by
  simp [WeierstrassCurve.Affine.Equation, WeierstrassCurve.Affine.evalEval_polynomial,
    WeierstrassCurve.CriticalCubic.equation, WeierstrassCurve.toAffine]

lemma criticalOriginSection (a b : k) :
    WeierstrassCurve.CriticalCubic.originSection k a b =
      (affinePointOver _ 0 0 (criticalOriginEquation a b)).left := by
  apply congrArg (fun φ : affineRing (WeierstrassCurve.CriticalCubic.equation k a b) →+* k =>
    Spec.map (CommRingCat.ofHom φ))
  apply affinePointEval_ext
  · intro c
    change (WeierstrassCurve.CriticalCubic.originMap k a b) (algebraMap k _ c) =
      affinePointEval _ 0 0 (criticalOriginEquation a b) (algebraMap k _ c)
    rw [AlgHom.commutes, affinePointEval_constant]
    rfl
  · simp
  · simp

/-- Equality transport only; it introduces no geometric comparison premise. -/
def affineEquationCastIso (V W : WeierstrassCurve k) (h : V = W) :
    Spec (.of (affineRing V)) ≅ Spec (.of (affineRing W)) :=
  eqToIso (congrArg (fun U => Spec (.of (affineRing U))) h)

@[reassoc] lemma affineEquationCastIso_structure (V W : WeierstrassCurve k) (h : V = W) :
    (affineEquationCastIso V W h).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k (affineRing W))) =
      Spec.map (CommRingCat.ofHom (algebraMap k (affineRing V))) := by
  subst W
  simp [affineEquationCastIso]

lemma affineEquationCastIso_point (V W : WeierstrassCurve k) (h : V = W)
    (x y : k) (heV : V.toAffine.Equation x y) (heW : W.toAffine.Equation x y) :
    (affinePointOver V x y heV).left ≫ (affineEquationCastIso V W h).hom =
      (affinePointOver W x y heW).left := by
  subst W
  change (affinePointOver V x y heV).left ≫ 𝟙 _ = (affinePointOver V x y heW).left
  rw [Category.comp_id]

variable (W : WeierstrassCurve k) (r s : k)
    (he : W.toAffine.Equation r s)
    (hx : W.toAffine.polynomialX.evalEval r s = 0)
    (hy : W.toAffine.polynomialY.evalEval r s = 0)

/-- The proved critical affine chart mapped into the original projective cubic. -/
def criticalChart : Spec (.of (affineRing (WeierstrassCurve.CriticalCubic.equation k W.a₁ (W.a₂ +
  3 * r)))) ⟶ scheme W :=
  (affineEquationCastIso _ _ (translate_eq_critical W r s he hx hy).symm).hom ≫
    (translatedAffineIso W r s).hom ≫ affineChart W

instance criticalChart_open : IsOpenImmersion (criticalChart W r s he hx hy) := by
  unfold criticalChart
  infer_instance

@[reassoc] lemma criticalChart_structure :
    criticalChart W r s he hx hy ≫ structureMap W =
      Spec.map (CommRingCat.ofHom (algebraMap k
        (affineRing (WeierstrassCurve.CriticalCubic.equation k W.a₁ (W.a₂ + 3 * r))))) := by
  simp only [criticalChart, Category.assoc, affineChart_structure,
    translatedAffineIso_structure, affineEquationCastIso_structure]

@[reassoc] lemma criticalChart_origin :
    WeierstrassCurve.CriticalCubic.originSection k W.a₁ (W.a₂ + 3 * r) ≫ criticalChart W r s he hx
      hy =
      (affinePointOver W r s he).left ≫ affineChart W := by
  rw [WeierstrassCurve.CriticalCubic.originSection, criticalChart]
  rw [← WeierstrassCurve.CriticalCubic.originSection, criticalOriginSection, ← Category.assoc]
  rw [affineEquationCastIso_point _ _ _ 0 0 _ (translatedOriginEquation W r s he)]
  exact translatedOrigin_projective W r s he

/-- The literal translated explicit normalization, extended into the same
original projective equation through its actual affine chart. -/
def originalNormalization (H : NormalProperCurveGenericExtension.{u}) :
    ProjectiveLine.projectiveP1 k ⟶ scheme W :=
  WeierstrassCurve.CriticalCubic.TargetNormalization.normalization k W.a₁ (W.a₂ + 3 * r)
    (structureMap W)
    (criticalChart W r s he hx hy) (criticalChart_structure W r s he hx hy) H

instance originalNormalization_dominant (H : NormalProperCurveGenericExtension.{u}) :
    IsDominant (originalNormalization W r s he hx hy H) := by
  unfold originalNormalization
  infer_instance

instance originalNormalization_functionField_isIso (H : NormalProperCurveGenericExtension.{u}) :
    IsIso (CommRingCat.ofHom (AlgebraicGeometry.Scheme.functionFieldMap
      (originalNormalization W r s he hx hy H))) := by
  unfold originalNormalization
  infer_instance

@[reassoc] lemma originalNormalization_over (H : NormalProperCurveGenericExtension.{u}) :
    originalNormalization W r s he hx hy H ≫ structureMap W = ProjectiveLine.structureMap k :=
  WeierstrassCurve.CriticalCubic.TargetNormalization.normalization_over _ _ _ _ _ _ _


end WeierstrassCurve.CriticalCubic.SingularNormalization
end
end SingularCubicBranchComparison
