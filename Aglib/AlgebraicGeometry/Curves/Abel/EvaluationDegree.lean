/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.RankOneFamily
public import Aglib.AlgebraicGeometry.Curves.Abel.FiniteCartierDegree
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Regularity
public import Aglib.AlgebraicGeometry.Curves.Picard.Degree.ProperCurveProductFormula

/-!
# Scheme degree of the actual evaluation divisor

The evaluation ideal has the negative degree of the original fibre line
bundle: its direct-image correction is pulled back from the field and has
zero Picard class. Actual Cartier ideal base change and the native finite
Cartier degree theorem therefore identify the finite evaluation fibre's
scheme degree with that original line-bundle degree.

The integer cast of the natural scheme degree is explicit. This measures
scheme length with residue-field weights, not point cardinality, and it
allows an empty degree-zero divisor. No function-field degree, perfectness,
theta, or principal-polarization hypothesis is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme Scheme.Hom Scheme.Cohomology Scheme.Modules Scheme.Modules.Hom Scheme.Modules.Invertible
open Scheme.OverField.Curve.Picard.Degree

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel

variable {Z S : Scheme.{u}} [IsLocallyNoetherian S]
  (f : Z ⟶ S) [IsProper f] [LocallyOfFinitePresentation f] [Flat f]
  (L : LineBundle Z) (hL : FibreCohomologyConcentrated f L.val 1)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original evaluation ideal has negative fibre degree, with no
restriction to degree one. -/
theorem evaluationIdeal_fibre_degree_eq_neg (K : Type u) [Field K]
    (t : Spec (.of K) ⟶ S) (hY : Properties (Over.mk (pullback.snd f t))) :
    curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension properCurveProductFormula
      (Over.mk (pullback.snd f t)) hY
      (pullbackClass (pullback.fst f t) (classOf Z (evaluationIdealLineBundle f L hL))) =
        -curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
          smoothClosedPointDimension smoothFieldDimension properCurveProductFormula
          (Over.mk (pullback.snd f t)) hY
          (classOf _ (pullbackLineBundle (pullback.fst f t) L)) := by
  let deg := curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
    smoothClosedPointDimension smoothFieldDimension properCurveProductFormula
    (Over.mk (pullback.snd f t)) hY
  change deg (pullbackClass (pullback.fst f t)
    (-classOf Z L + pullbackClass f (classOf S (directImageLineBundle f L hL)))) =
      -deg (classOf _ (pullbackLineBundle (pullback.fst f t) L))
  rw [PullbackTensor.Local.pullbackClass_add, PullbackTensor.Local.pullbackClass_neg,
    fibre_baseClass_zero, add_zero, map_neg, pullbackClass_classOf]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual finite evaluation fibre has scheme degree equal to the
original pulled line-bundle degree. The natural/integer relation is explicit. -/
theorem evaluationZero_fibre_degree
    [Mono (evaluationContraction f L hL)]
    [Flat (zeroInclusion (evaluationContraction f L hL) ≫ f)]
    [IsFinite (zeroInclusion (evaluationContraction f L hL) ≫ f)]
    (K : Type u) [Field K] (t : Spec (.of K) ⟶ S)
    (hY : Properties (Over.mk (pullback.snd f t))) :
    (finiteSchemeDegree K
      (pullback.snd (zeroInclusion (evaluationContraction f L hL) ≫ f) t) : ℤ) =
        curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
          smoothClosedPointDimension smoothFieldDimension properCurveProductFormula
          (Over.mk (pullback.snd f t)) hY
          (classOf _ (pullbackLineBundle (pullback.fst f t) L)) := by
  let I := evaluationIdealLineBundle f L hL
  let φ := evaluationContraction f L hL
  let i := zeroInclusion φ
  let J := Hom.fibreIdealLineBundle f i t Hom.relativeCartierIdealBaseChange
    (zeroIdealLineBundle I φ).property
  have hj : classOf (pullback f t) J = pullbackClass (pullback.fst f t) (classOf Z I) := by
    rw [Hom.fibreIdealLineBundle_class]
    exact congrArg (pullbackClass (pullback.fst f t)) (zeroIdealLineBundle_class I φ)
  have hn := evaluationIdeal_fibre_degree_eq_neg f L hL K t hY
  have : IsFinite (Hom.fibreInclusion f i t ≫ pullback.snd f t) := by
    rw [Hom.fibreInclusion_snd]
    infer_instance
  have : IsFinite (Hom.fibreInclusion f i t ≫ (Over.mk (pullback.snd f t)).hom) :=
    inferInstanceAs (IsFinite (Hom.fibreInclusion f i t ≫ pullback.snd f t))
  have he := curveDegree_dualIdeal smoothFieldNormality normalComponentsOpen
    smoothFieldRegularity smoothClosedPointDimension smoothFieldDimension properCurveProductFormula
    FiniteCartierDegree.finiteCartierIdealDegree (Over.mk (pullback.snd f t)) hY
    (Hom.fibreInclusion f i t) J.property
  change curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
    smoothClosedPointDimension smoothFieldDimension properCurveProductFormula
    (Over.mk (pullback.snd f t)) hY (-classOf (pullback f t) J) =
      (finiteSchemeDegree K (Hom.fibreInclusion f i t ≫ pullback.snd f t) : ℤ) at he
  rw [map_neg, hj, hn, neg_neg, Hom.fibreInclusion_snd] at he
  exact he.symm

end AlgebraicGeometry.Scheme.OverField.Curve.Abel

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel

local instance : MorphismProperty.IsStableUnderBaseChange
    (@SmoothOfRelativeDimension.{u} 1) :=
  smoothOfRelativeDimension_isStableUnderBaseChange 1

variable {Z S : Scheme.{u}} [IsLocallyNoetherian S]
  (f : Z ⟶ S) [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]
  (L : LineBundle Z)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On the constructed rank-one open of a genuine relative curve, every
Cartier, monicity, finiteness, and flatness premise of the degree comparison
is discharged by the native evaluation construction. -/
theorem rankOneEvaluation_fibre_degree (K : Type u) [Field K]
    (t : Spec (.of K) ⟶ (rankOneOpen f L).toScheme) :
    let p := pullback.snd f (rankOneOpen f L).ι
    letI : SmoothOfRelativeDimension 1 p := MorphismProperty.pullback_snd _ _ inferInstance
    (finiteSchemeDegree K (pullback.snd (zeroInclusion (rankOneEvaluation f L) ≫ p) t) : ℤ) =
      curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
        smoothClosedPointDimension smoothFieldDimension properCurveProductFormula
        (Over.mk (pullback.snd p t)) (rankOneFamily_fibre_properties p K t)
        (classOf _ (pullbackLineBundle (pullback.fst p t) (rankOneBundle f L))) := by
  let p := pullback.snd f (rankOneOpen f L).ι
  have : SmoothOfRelativeDimension 1 p := MorphismProperty.pullback_snd _ _ inferInstance
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have : Mono (evaluationContraction p (rankOneBundle f L) (rankOneConcentration f L)) :=
    mono_rankOneEvaluation f L
  obtain ⟨hf, hflat, -⟩ := rankOneEvaluation_finite_flat f L
  have : IsFinite (zeroInclusion
      (evaluationContraction p (rankOneBundle f L) (rankOneConcentration f L)) ≫ p) := hf
  have : Flat (zeroInclusion
      (evaluationContraction p (rankOneBundle f L) (rankOneConcentration f L)) ≫ p) := hflat
  exact evaluationZero_fibre_degree p (rankOneBundle f L) (rankOneConcentration f L)
    K t (rankOneFamily_fibre_properties p K t)

end AlgebraicGeometry.Scheme.OverField.Curve.Abel
