/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.EvaluationSection
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Graph
public import Aglib.AlgebraicGeometry.Curves.Abel.Degree
public import Aglib.AlgebraicGeometry.Curves.Abel.Evaluation
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Regular
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Fibre
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.FibreClass
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.RankOne
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Relative
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Rank
public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
# Degree one for the actual evaluation zero divisor

The canonical 056Q ideal comparison identifies each actual fibre ideal with
the pullback of the evaluation ideal. Its class is minus the given degree-one
class: the pulled direct-image factor has degree zero because Pic(Spec K)=0.
The existing general finite Cartier ideal-degree theorem then computes the
actual fibre coordinate-algebra dimension as one. The pinned native finite
flat rank criterion proves that the projection is an isomorphism. The class
recovery equation is proved from the actual ideal-factor isomorphism.

Every algebraically closed field and every structural point is retained.
Monicity, flatness and finiteness are discharged from actual evaluation
geometric regularity and the two general relative Cartier families. The
resulting inverse projection constructs an actual section on every locally
Noetherian base. No new
Cartier degree, degree-one isomorphism or Abel inverse premise is introduced.
Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
-/

open _root_.AlgebraicGeometry.Scheme
  (NormalComponentsOpen SmoothClosedPointDimension SmoothFieldDimension SmoothFieldNormality
    SmoothFieldRegularity)
open _root_.AlgebraicGeometry.Scheme.Cohomology
  (FibreCohomologyConcentrated)
open AlgebraicGeometry.Scheme.Modules.Invertible
  (IsLocallyRankOne LineBundle PicardGroup classOf classOf_dual dualLineBundle pullbackClass
    pullbackClass_comp pullbackClass_zero pullbackLineBundle)
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/

@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Cohomology
  (evaluationIdealLineBundle directImageLineBundle evaluationContraction)
open AlgebraicGeometry.Scheme.Modules.Hom (zeroInclusion)
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.RelativePicard.Classes
open AlgebraicGeometry.Scheme
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel
universe u
open Picard AlgebraicGeometry.Scheme.Hom Divisors
variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (htensor : ModuleTensorPullback.{u})
variable {Z S : Scheme.{u}} (f : Z ⟶ S)
theorem fibre_baseClass_zero (P : PicardGroup S) (K : Type u) [Field K] (t : Spec (.of K) ⟶ S) :
    pullbackClass (pullback.fst f t) (pullbackClass f P) = 0 := by
  rw [← pullbackClass_comp, pullback.condition, pullbackClass_comp]
  rw [fieldPicard_eq_zero K (pullbackClass t P), pullbackClass_zero]

variable [IsLocallyNoetherian S]
variable [IsProper f] [LocallyOfFinitePresentation f] [Flat f]
variable (L : LineBundle Z) (hL : FibreCohomologyConcentrated f L.val 1)
include htensor in
theorem evaluationIdeal_fibre_degree (K : Type u) [Field K] (t : Spec (.of K) ⟶ S)
    (hY : Properties (Over.mk (pullback.snd f t)))
    (hd : curveDegree hnormal hcomp hreg hclosed hdim hprod
      (Over.mk (pullback.snd f t)) hY (classOf _ (pullbackLineBundle (pullback.fst f t) L)) = 1) :
    curveDegree hnormal hcomp hreg hclosed hdim hprod (Over.mk (pullback.snd f t)) hY
      (pullbackClass (pullback.fst f t) (classOf Z (evaluationIdealLineBundle f L hL))) = -1 := by
  change curveDegree hnormal hcomp hreg hclosed hdim hprod (Over.mk (pullback.snd f t)) hY
    (pullbackClass (pullback.fst f t) (-classOf Z L +
      pullbackClass f (classOf S (directImageLineBundle f L hL)))) = -1
  rw [pullbackClass_add htensor, pullbackClass_neg htensor, fibre_baseClass_zero,
    add_zero, map_neg]
  exact congrArg Neg.neg hd

variable (hcartier : FiniteCartierIdealDegree.{u})
include hcartier in
theorem curveDegree_dualIdeal {K : Type u} [Field K] (Y : FScheme K) (hY : Properties Y)
    {D : Scheme.{u}} (i : D ⟶ Y.left) [IsClosedImmersion i] [IsFinite (i ≫ Y.hom)]
    (hI : IsLocallyRankOne Y.left (idealModule i)) :
    curveDegree hnormal hcomp hreg hclosed hdim hprod Y hY
      (classOf Y.left (dualLineBundle Y.left ⟨idealModule i, hI⟩)) =
        (finiteSchemeDegree K (i ≫ Y.hom) : ℤ) := by
  letI := curveProperties_isIntegral hnormal hcomp hY
  letI := curveProperties_isNoetherian hY
  letI (x : ClosedPoint Y.left) : IsDiscreteValuationRing (Y.left.presheaf.stalk x.val) :=
    curveProperties_closedPoint_stalk_dvr hnormal hreg hclosed hY x.val x.property
  letI := hY.proper
  exact hcartier K Y.left D Y.hom i (le_of_eq (curveProperties_dimension hdim hY))
    (hprod K Y.left Y.hom (curveProperties_dimension hdim hY)) hI inferInstance inferInstance
      inferInstance

variable (hbase : RelativeCartierIdealBaseChange.{u})
include hcartier hbase htensor in
theorem evaluationZero_fibre_degree_one
    [Mono (evaluationContraction f L hL)]
    [Flat (zeroInclusion (evaluationContraction f L hL) ≫ f)]
    [IsFinite (zeroInclusion (evaluationContraction f L hL) ≫ f)]
    (K : Type u) [Field K] (t : Spec (.of K) ⟶ S)
    (hY : Properties (Over.mk (pullback.snd f t)))
    (hd : curveDegree hnormal hcomp hreg hclosed hdim hprod
      (Over.mk (pullback.snd f t)) hY (classOf _ (pullbackLineBundle (pullback.fst f t) L)) = 1) :
    finiteSchemeDegree K (pullback.snd (zeroInclusion (evaluationContraction f L hL) ≫ f) t) = 1
      := by
  let I := evaluationIdealLineBundle f L hL
  let φ := evaluationContraction f L hL
  let i := zeroInclusion φ
  let J := fibreIdealLineBundle f i t hbase (zeroIdealLineBundle I φ).property
  have hj : classOf (pullback f t) J = pullbackClass (pullback.fst f t) (classOf Z I) := by
    rw [fibreIdealLineBundle_class]
    exact congrArg (pullbackClass (pullback.fst f t)) (zeroIdealLineBundle_class I φ)
  have hn := evaluationIdeal_fibre_degree hnormal hcomp hreg hclosed hdim hprod htensor
    f L hL K t hY hd
  haveI : IsFinite (fibreInclusion f i t ≫ pullback.snd f t) := by
    rw [fibreInclusion_snd]
    infer_instance
  haveI : IsFinite (fibreInclusion f i t ≫ (Over.mk (pullback.snd f t)).hom) :=
    inferInstanceAs (IsFinite (fibreInclusion f i t ≫ pullback.snd f t))
  have he := curveDegree_dualIdeal hnormal hcomp hreg hclosed hdim hprod hcartier
    (Over.mk (pullback.snd f t)) hY (fibreInclusion f i t) J.property
  change curveDegree hnormal hcomp hreg hclosed hdim hprod (Over.mk (pullback.snd f t)) hY
    (-classOf (pullback f t) J) = (finiteSchemeDegree K (fibreInclusion f i t ≫ pullback.snd f t)
      : ℤ) at he
  rw [map_neg, hj, hn, neg_neg, fibreInclusion_snd] at he
  exact_mod_cast he.symm

include hcartier hbase htensor in
theorem evaluationZero_isIso
    [Mono (evaluationContraction f L hL)]
    [Flat (zeroInclusion (evaluationContraction f L hL) ≫ f)]
    [IsFinite (zeroInclusion (evaluationContraction f L hL) ≫ f)]
    (hcurves : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      Properties (Over.mk (pullback.snd f t)))
    (hd : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      curveDegree hnormal hcomp hreg hclosed hdim hprod
        (Over.mk (pullback.snd f t)) (hcurves K t)
        (classOf _ (pullbackLineBundle (pullback.fst f t) L)) = 1) :
    IsIso (zeroInclusion (evaluationContraction f L hL) ≫ f) := by
  apply AlgebraicGeometry.Scheme.Hom.FiniteFlat.isIso_of_geometricFibre_dimension_one
  intro K _ _ t
  exact evaluationZero_fibre_degree_one hnormal hcomp hreg hclosed hdim hprod htensor
    f L hL hcartier hbase K t (hcurves K t) (hd K t)

theorem evaluationZero_class_recovery [Mono (evaluationContraction f L hL)] :
    classOf Z L = classOf Z (dualLineBundle Z
      (zeroIdealLineBundle (evaluationIdealLineBundle f L hL)
        (evaluationContraction f L hL))) +
      pullbackClass f (classOf S (directImageLineBundle f L hL)) := by
  rw [classOf_dual, zeroIdealLineBundle_class]
  change classOf Z L = -(-classOf Z L +
    pullbackClass f (classOf S (directImageLineBundle f L hL))) + _
  abel
end AlgebraicGeometry.Scheme.OverField.Curve.Abel

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel
universe u
open Picard AlgebraicGeometry.Scheme.Hom Divisors
variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (htensor : ModuleTensorPullback.{u})
variable (hcartier : FiniteCartierIdealDegree.{u}) (hbase : RelativeCartierIdealBaseChange.{u})
variable (hregular : FibrewiseRegularLineBundle.{u}) (hlocal : SmoothRelativeCartierLocality.{u})
variable {Z S : Scheme.{u}} (f : Z ⟶ S)
variable [IsLocallyNoetherian S]
variable [IsProper f] [LocallyOfFinitePresentation f] [Flat f]
variable (L : LineBundle Z) (hL : FibreCohomologyConcentrated f L.val 1)
include hnormal hcomp hregular hlocal in
theorem evaluationZero_finite_flat [SmoothOfRelativeDimension 1 f]
    (hcurves : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      Properties (Over.mk (pullback.snd f t))) :
    IsFinite (zeroInclusion (evaluationContraction f L hL) ≫ f) ∧
      Flat (zeroInclusion (evaluationContraction f L hL) ≫ f) ∧
      LocallyOfFinitePresentation (zeroInclusion (evaluationContraction f L hL) ≫ f) :=
  regularZero_finite_flat f (evaluationIdealLineBundle f L hL)
    (evaluationContraction f L hL) hregular hlocal
    (evaluationContraction_geometric_regular f L hL hnormal hcomp hcurves)

include hregular hlocal hcartier hbase htensor in
theorem evaluationZero_projection_isIso [SmoothOfRelativeDimension 1 f]
    (hcurves : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      Properties (Over.mk (pullback.snd f t)))
    (hd : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      curveDegree hnormal hcomp hreg hclosed hdim hprod
        (Over.mk (pullback.snd f t)) (hcurves K t)
        (classOf _ (pullbackLineBundle (pullback.fst f t) L)) = 1) :
    IsIso (zeroInclusion (evaluationContraction f L hL) ≫ f) := by
  have hφ := evaluationContraction_geometric_regular f L hL hnormal hcomp hcurves
  letI := (hregular Z S f (evaluationIdealLineBundle f L hL)
    (evaluationContraction f L hL) inferInstance inferInstance hφ).1
  obtain ⟨hfinite, hflat, _⟩ := evaluationZero_finite_flat hnormal hcomp hregular hlocal
    f L hL hcurves
  letI := hfinite
  letI := hflat
  exact evaluationZero_isIso hnormal hcomp hreg hclosed hdim hprod htensor
    f L hL hcartier hbase hcurves hd
end AlgebraicGeometry.Scheme.OverField.Curve.Abel
