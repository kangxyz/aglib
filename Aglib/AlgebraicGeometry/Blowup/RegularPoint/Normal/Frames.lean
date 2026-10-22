/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.RegularPoint
public import Aglib.AlgebraicGeometry.Blowup.IdealFrames.Transition
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local

/-!
# Original kernel and normal frames of a regular-point blowup

The frames come from the actual denominator multiplication on the original saturated
charts. Their original inclusion, reciprocal-overlap and Laurent-reduction equations
are retained. The actual normal object is the restricted dual of the actual kernel.
The projective twisting comparison is the consumer in `RegularPoint.Normal`.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open Scheme.Hom Scheme.Modules Scheme.Modules.Invertible
open Scheme.Blowup.IdealFrames

universe u

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

section DualFrame

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : LineBundle Y)
  (e : SheafOfModules.unit X.ringCatSheaf ≅ (Scheme.Modules.pullback f).obj L.val)

/-- Evaluation against the given actual pulled-back frame trivializes the pulled-back dual.
All arrows are the native unit, tensor comparison, braiding, and evaluation arrows. -/
def dualPullbackFrame :
    SheafOfModules.unit X.ringCatSheaf ≅ (Scheme.Modules.pullback f).obj (dualLineBundle Y L).val :=
  ((tensorSheafLeftUnit X ((Scheme.Modules.pullback f).obj (dualLineBundle Y L).val)).symm ≪≫
    tensorSheafIso X e (Iso.refl _) ≪≫
    tensorSheafBraiding X ((Scheme.Modules.pullback f).obj L.val)
      ((Scheme.Modules.pullback f).obj (dualLineBundle Y L).val) ≪≫
    (PullbackTensor.Local.pullbackLineBundleTensorIso f (dualLineBundle Y L) L).symm ≪≫
    (Scheme.Modules.pullback f).mapIso (dualEvaluationIso Y L) ≪≫ pullbackUnitIso f).symm

/-- The actual dual frame is inverse to evaluation against the original frame. -/
@[reassoc]
theorem dualPullbackFrame_evaluation :
    (dualPullbackFrame f L e).hom ≫
        (tensorSheafLeftUnit X ((Scheme.Modules.pullback f).obj (dualLineBundle Y L).val)).inv ≫
        (tensorSheafIso X e (Iso.refl _)).hom ≫
        (tensorSheafBraiding X ((Scheme.Modules.pullback f).obj L.val)
          ((Scheme.Modules.pullback f).obj (dualLineBundle Y L).val)).hom ≫
        (PullbackTensor.Local.pullbackLineBundleTensorIso f (dualLineBundle Y L) L).inv ≫
        (Scheme.Modules.pullback f).map (dualEvaluationIso Y L).hom ≫ (pullbackUnitIso f).hom =
      𝟙 (SheafOfModules.unit X.ringCatSheaf) :=
  (dualPullbackFrame f L e).hom_inv_id

end DualFrame

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The actual inverse-image-centre scheme of the same constructed blowup. -/
abbrev centreScheme : Scheme.{u} := ((affineCenter A I).comap (blowdown I)).subscheme

/-- The original inverse-image-centre ideal is an actual invertible module. -/
def centreIdealLine : LineBundle (canonicalBlowup I) :=
  ⟨idealModule ((affineCenter A I).comap (blowdown I)).subschemeι,
    (blowupDatum (affineCenter A I)).cartier⟩

/-- The actual conormal line is restriction of the actual kernel ideal. -/
def centreConormalLine : LineBundle ((affineCenter A I).comap (blowdown I)).subscheme :=
  pullbackLineBundle ((affineCenter A I).comap (blowdown I)).subschemeι (centreIdealLine I)

/-- The actual normal line, with the same definition used by `actualSelfIntersection`. -/
def centreNormalLine : LineBundle ((affineCenter A I).comap (blowdown I)).subscheme :=
  pullbackLineBundle ((affineCenter A I).comap (blowdown I)).subschemeι
    (dualLineBundle (canonicalBlowup I) (centreIdealLine I))

variable (a b : A) (hI : Ideal.span {a, b} = I)
  (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)

/-- The original polynomial chart on the actual inverse-image centre. -/
def centreChart : Spec (.of (Polynomial (A ⧸ I))) ⟶
    ((affineCenter A I).comap (blowdown I)).subscheme :=
  fibreChart I a b hI ha hb ≫ (centreFibreIso I).inv

/-- The original centre-chart inclusion retains the saturated-chart reduction. -/
@[reassoc]
theorem centreChart_ι :
    centreChart I a b hI ha hb ≫ ((affineCenter A I).comap (blowdown I)).subschemeι =
      chartFibreToBlowup I a b hI ha hb := by
  have ht : (centreFibreIso I).inv ≫
      ((affineCenter A I).comap (blowdown I)).subschemeι = exceptionalι I := by
    apply (cancel_epi (centreFibreIso I).hom).mp
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, centreFibreIso_hom_ι]
  rw [centreChart, Category.assoc, ht, fibreChart_fst]

@[reassoc]
theorem centreChart_over :
    centreChart I a b hI ha hb ≫ centreStructureMap I =
      Scheme.PolynomialLaurent.polynomialProjection (.of (A ⧸ I)) := by
  simp only [centreChart, centreStructureMap, Category.assoc, Iso.inv_hom_id_assoc,
    fibreChart_snd]

instance centreChartIsOpenImmersion : IsOpenImmersion (centreChart I a b hI ha hb) := by
  unfold centreChart
  infer_instance

/-- Pullback of the original ideal frame along the actual fibre-ring reduction. -/
def reducedIdealFrame :
    SheafOfModules.unit (Spec (.of (Polynomial (A ⧸ I)))).ringCatSheaf ≅
      (Scheme.Modules.pullback (chartFibreToBlowup I a b hI ha hb)).obj (centreIdealLine I).val :=
  frameAlong
    (Spec.map (CommRingCat.ofHom (chartFibreRingMap I a b hI ha hb).toRingHom))
    (chartMap (blowupDatum (affineCenter A I)) (firstGenerator I a b hI))
    (centreIdealLine I).val
    (IdealFrames.chartFrame (blowupDatum (affineCenter A I)) (firstGenerator I a b hI))

/-- The actual conormal frame on the original polynomial chart. -/
def conormalChartFrame :
    SheafOfModules.unit (Spec (.of (Polynomial (A ⧸ I)))).ringCatSheaf ≅
      (Scheme.Modules.pullback (centreChart I a b hI ha hb)).obj (centreConormalLine I).val :=
  reducedIdealFrame I a b hI ha hb ≪≫
    ((pullbackCongr (centreChart_ι I a b hI ha hb)).app (centreIdealLine I).val).symm ≪≫
    ((pullbackComp _ _).app (centreIdealLine I).val).symm

/-- The actual normal frame is dual evaluation against the original parameter frame,
transported through the original centre-chart inclusion triangle. -/
def normalChartFrame :
    SheafOfModules.unit (Spec (.of (Polynomial (A ⧸ I)))).ringCatSheaf ≅
      (Scheme.Modules.pullback (centreChart I a b hI ha hb)).obj (centreNormalLine I).val :=
  dualPullbackFrame (chartFibreToBlowup I a b hI ha hb) (centreIdealLine I)
      (reducedIdealFrame I a b hI ha hb) ≪≫
    ((pullbackCongr (centreChart_ι I a b hI ha hb)).app
      (dualLineBundle (canonicalBlowup I) (centreIdealLine I)).val).symm ≪≫
    ((pullbackComp _ _).app (dualLineBundle (canonicalBlowup I) (centreIdealLine I)).val).symm

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

variable (A : Type u) [CommRing A] [IsRegularLocalRing A] (hd : ringKrullDim A = 2)

/-- The first actual centre chart uses the original chosen first regular parameter. -/
abbrev firstCentreChart :=
  centreChart (maximalIdeal A) (firstParameter A hd) (secondParameter A hd)
    (parameters_spec A hd).2.2.1 (parameters_spec A hd).2.2.2.1
    (parameters_spec A hd).2.2.2.2.1

/-- The second actual centre chart uses the same original parameters in the opposite order. -/
abbrev secondCentreChart :=
  centreChart (maximalIdeal A) (secondParameter A hd) (firstParameter A hd)
    (Ideal.span_pair_comm.trans (parameters_spec A hd).2.2.1)
    (parameters_spec A hd).2.2.2.2.2.1 (parameters_spec A hd).2.2.2.2.2.2

/-- The first centre chart is the standard first chart under the fixed P1 comparison. -/
@[reassoc]
theorem firstCentreChart_projectiveP1 :
    firstCentreChart A hd ≫ (centreOverIsoProjectiveP1 A hd).hom.left =
      ProjectiveLine.chart (ResidueField A) 0 := by
  change (firstFibreChart A hd ≫ (centreFibreIso (maximalIdeal A)).inv) ≫
    ((centreFibreIso (maximalIdeal A)).hom ≫ (exceptionalOverIsoProjectiveP1 A hd).hom.left) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc, firstFibreChart_projectiveP1]

/-- The second centre chart is the standard second chart under that same P1 comparison. -/
@[reassoc]
theorem secondCentreChart_projectiveP1 :
    secondCentreChart A hd ≫ (centreOverIsoProjectiveP1 A hd).hom.left =
      ProjectiveLine.chart (ResidueField A) 1 := by
  change (secondFibreChart A hd ≫ (centreFibreIso (maximalIdeal A)).inv) ≫
    ((centreFibreIso (maximalIdeal A)).hom ≫ (exceptionalOverIsoProjectiveP1 A hd).hom.left) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc, secondFibreChart_projectiveP1]

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Localization.Away
open Scheme.Modules Scheme.Modules.Invertible IdealFrames

variable {A : Type u} [CommRing A] (I : Ideal A) (a b : A)
  (hI : Ideal.span {a, b} = I) (ha : IsSMulRegular A a)
  (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)

/-- The original first saturated chart maps to the original reciprocal overlap algebra. -/
def firstOverlapRingMap : affineBlowupAlgebra A I a →ₐ[A]
    Localization.Away (pairCoordinate a b) :=
  (IsScalarTower.toAlgHom A (pairQuotient a b) (Localization.Away (pairCoordinate a b))).comp
    (chartAlgebraEquiv I a b hI ha hb).symm.toAlgHom

variable (hb' : IsSMulRegular A b) (ha' : IsSMulRegular (A ⧸ Ideal.span {b}) a)

/-- The opposite saturated chart maps to that same original overlap via the actual reciprocal. -/
def secondOverlapRingMap : affineBlowupAlgebra A I b →ₐ[A]
    Localization.Away (pairCoordinate a b) :=
  (pairReciprocal a b).comp
    (chartAlgebraEquiv I b a (Ideal.span_pair_comm.trans hI) hb' ha').symm.toAlgHom

/-- Both original saturated charts retain the actual pre-fibre reciprocal equation. -/
theorem overlapRingMaps_chart :
    Spec.map (CommRingCat.ofHom (firstOverlapRingMap I a b hI ha hb).toRingHom) ≫
        IdealFrames.chartMap (blowupDatum (affineCenter A I)) (firstGenerator I a b hI) =
      Spec.map (CommRingCat.ofHom (secondOverlapRingMap I a b hI hb' ha').toRingHom) ≫
        IdealFrames.chartMap (blowupDatum (affineCenter A I))
          (firstGenerator I b a (Ideal.span_pair_comm.trans hI)) := by
  change Spec.map (CommRingCat.ofHom (chartAlgebraEquiv I a b hI ha hb).symm.toRingHom ≫
      CommRingCat.ofHom (algebraMap (pairQuotient a b)
        (Localization.Away (pairCoordinate a b)))) ≫ _ =
    Spec.map (CommRingCat.ofHom
      (chartAlgebraEquiv I b a (Ideal.span_pair_comm.trans hI) hb' ha').symm.toRingHom ≫
      CommRingCat.ofHom (pairReciprocal a b).toRingHom) ≫ _
  rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc]
  exact rawChart_reciprocal I a b hI ha hb hb' ha'

instance firstOverlapChartIsOpenImmersion : IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (firstOverlapRingMap I a b hI ha hb).toRingHom) ≫
      IdealFrames.chartMap (blowupDatum (affineCenter A I)) (firstGenerator I a b hI)) := by
  change IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (chartAlgebraEquiv I a b hI ha hb).symm.toRingHom ≫
      CommRingCat.ofHom (algebraMap (pairQuotient a b)
        (Localization.Away (pairCoordinate a b)))) ≫ _)
  rw [Spec.map_comp, Category.assoc]
  change IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap (pairQuotient a b)
      (Localization.Away (pairCoordinate a b)))) ≫ rawChart I a b hI ha hb)
  infer_instance

/-- The opposite denominator is the first denominator times the literal overlap coordinate. -/
theorem overlapRingMaps_denominator :
    secondOverlapRingMap I a b hI hb' ha'
        (algebraMap A (affineBlowupAlgebra A I b) b) =
      algebraMap (pairQuotient a b) (Localization.Away (pairCoordinate a b))
          (pairCoordinate a b) *
        firstOverlapRingMap I a b hI ha hb
          (algebraMap A (affineBlowupAlgebra A I a) a) := by
  rw [(secondOverlapRingMap I a b hI hb' ha').commutes,
    (firstOverlapRingMap I a b hI ha hb).commutes]
  rw [IsScalarTower.algebraMap_apply A (pairQuotient a b)
    (Localization.Away (pairCoordinate a b)) b, ← pairCoordinate_relation, map_mul,
    ← IsScalarTower.algebraMap_apply A (pairQuotient a b)
      (Localization.Away (pairCoordinate a b)) a, mul_comm]

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory AlgebraicGeometry Localization.Away
open Scheme.PolynomialLaurent

variable {A : Type u} [CommRing A] (I : Ideal A) (a b : A)
  (hI : Ideal.span {a, b} = I) (ha : IsSMulRegular A a)
  (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)

/-- The original overlap coordinate as a literal unit with the original reciprocal inverse. -/
def rawOverlapUnit : (Localization.Away (pairCoordinate a b))ˣ where
  val := algebraMap (pairQuotient a b) (Localization.Away (pairCoordinate a b))
    (pairCoordinate a b)
  inv := IsLocalization.Away.invSelf (pairCoordinate a b)
  val_inv := IsLocalization.Away.mul_invSelf (pairCoordinate a b)
  inv_val := by rw [mul_comm, IsLocalization.Away.mul_invSelf]

/-- The original overlap unit reduces to the original positive Laurent unit. -/
theorem rawLaurentLift_overlapUnit :
    Units.map (rawLaurentLift I a b hI ha hb).toRingHom.toMonoidHom (rawOverlapUnit a b) =
      laurentCoordinateUnit (.of (A ⧸ I)) := by
  apply Units.ext
  change rawLaurentLift I a b hI ha hb
    (algebraMap (pairQuotient a b) (Localization.Away (pairCoordinate a b))
      (pairCoordinate a b)) = LaurentPolynomial.T 1
  rw [rawLaurentLift_base, rawLaurentMap_coordinate]

/-- The first saturated chart specializes through the same actual Laurent polynomial map. -/
theorem firstOverlapRingMap_laurent :
    (rawLaurentLift I a b hI ha hb).comp (firstOverlapRingMap I a b hI ha hb) =
      ((Polynomial.toLaurentAlg (R := A ⧸ I)).restrictScalars A).comp
        (chartFibreRingMap I a b hI ha hb) := by
  apply AlgHom.ext
  intro x
  change rawLaurentLift I a b hI ha hb
    (algebraMap (pairQuotient a b) (Localization.Away (pairCoordinate a b))
      ((chartAlgebraEquiv I a b hI ha hb).symm x)) = _
  rw [rawLaurentLift_base]
  change Polynomial.toLaurent (chartFibreRingMap I a b hI ha hb
    (chartAlgebraEquiv I a b hI ha hb ((chartAlgebraEquiv I a b hI ha hb).symm x))) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

variable (hb' : IsSMulRegular A b) (ha' : IsSMulRegular (A ⧸ Ideal.span {b}) a)

/-- The opposite saturated chart specializes through the original inverse Laurent map. -/
theorem secondOverlapRingMap_laurent :
    (rawLaurentLift I a b hI ha hb).comp (secondOverlapRingMap I a b hI hb' ha') =
      ((LaurentPolynomial.invert (R := A ⧸ I)).restrictScalars A).toAlgHom.comp
        (((Polynomial.toLaurentAlg (R := A ⧸ I)).restrictScalars A).comp
          (chartFibreRingMap I b a (Ideal.span_pair_comm.trans hI) hb' ha')) := by
  apply AlgHom.ext
  intro x
  have h := congrArg
    (fun f : pairQuotient b a →ₐ[A] LaurentPolynomial (A ⧸ I) =>
      f ((chartAlgebraEquiv I b a (Ideal.span_pair_comm.trans hI) hb' ha').symm x))
    (rawLaurentLift_reciprocal I a b hI ha hb hb' ha')
  change rawLaurentLift I a b hI ha hb
      (pairReciprocal a b ((chartAlgebraEquiv I b a
        (Ideal.span_pair_comm.trans hI) hb' ha').symm x)) =
    LaurentPolynomial.invert (Polynomial.toLaurent
      (chartFibreRingMap I b a (Ideal.span_pair_comm.trans hI) hb' ha'
        (chartAlgebraEquiv I b a (Ideal.span_pair_comm.trans hI) hb' ha'
          ((chartAlgebraEquiv I b a (Ideal.span_pair_comm.trans hI) hb' ha').symm x)))) at h
  rw [AlgEquiv.apply_symm_apply] at h
  exact h

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The original conormal and restricted dual pair to the structure module through the
native tensor pullback, braiding and evaluation. No flatness of the centre inclusion is used. -/
def centreNormalEvaluationIso :
    tensorSheaf ((affineCenter A I).comap (blowdown I)).subscheme
        (centreConormalLine I).val (centreNormalLine I).val ≅
      SheafOfModules.unit ((affineCenter A I).comap (blowdown I)).subscheme.ringCatSheaf :=
  (PullbackTensor.Local.pullbackLineBundleTensorIso
      ((affineCenter A I).comap (blowdown I)).subschemeι (centreIdealLine I)
      (dualLineBundle (canonicalBlowup I) (centreIdealLine I))).symm ≪≫
    (Scheme.Modules.pullback ((affineCenter A I).comap (blowdown I)).subschemeι).mapIso
      (tensorSheafBraiding (canonicalBlowup I) (centreIdealLine I).val
        (dualLineBundle (canonicalBlowup I) (centreIdealLine I)).val ≪≫
        dualEvaluationIso (canonicalBlowup I) (centreIdealLine I)) ≪≫
    pullbackUnitIso ((affineCenter A I).comap (blowdown I)).subschemeι

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory AlgebraicGeometry Localization.Away
open Scheme.Modules Scheme.Modules.Invertible IdealFrames Scheme.PolynomialLaurent

variable {A : Type u} [CommRing A] (I : Ideal A) (a b : A)
  (hI : Ideal.span {a, b} = I) (ha : IsSMulRegular A a)
  (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)

private theorem algHom_toRingHom_mul
    {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra R U]
    (f : S →ₐ[R] U) (g : T →ₐ[R] U) (x : S) (y : T) (r : U)
    (h : f x = r * g y) : f.toRingHom x = r * g.toRingHom y := h

private theorem transportInclusionEquation {C : Type*} [Category C] {U V W : C}
    {e e' : U ⟶ V} {i : V ⟶ W} {c : W ⟶ U} {s : U ⟶ U}
    (he : e = e') (h : e' ≫ i ≫ c = s) : e ≫ i ≫ c = s :=
  (congrArg (fun q => q ≫ i ≫ c) he).trans h

private theorem scalarFrameEquation {C : Type*} [Category C] {U V₀ V₁ : C}
    (e₀ : U ⟶ V₀) (e₁ : U ⟶ V₁) (q : V₁ ⟶ V₀)
    (i₀ : V₀ ⟶ U) (i₁ : V₁ ⟶ U) [Mono i₀]
    (s₀ s₁ r : U ⟶ U) (hq : q ≫ i₀ = i₁)
    (h₀ : e₀ ≫ i₀ = s₀) (h₁ : e₁ ≫ i₁ = s₁) (hr : s₁ = r ≫ s₀) :
    e₁ ≫ q = r ≫ e₀ := by
  apply (cancel_mono i₀).mp
  rw [Category.assoc, hq, h₁, Category.assoc, h₀, hr]

/-- Keep the literal native equal-map comparison together with its actual inclusion
square. The concrete consumer uses these projections without reducing an object cast. -/
opaque pullbackInclusionComparisonData {X Y : Scheme.{u}} {j k : X ⟶ Y}
    (h : j = k) (M : Y.Modules)
    (i : M ⟶ (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf)) :
    { e : (Scheme.Modules.pullback j).obj M ≅ (Scheme.Modules.pullback k).obj M //
      e.hom = (pullbackCongr h).hom.app M ∧
      e = (pullbackCongr h).app M ∧
      e.hom ≫ (Scheme.Modules.pullback k).map i ≫ (pullbackUnitIso k).hom =
        (Scheme.Modules.pullback j).map i ≫ (pullbackUnitIso j).hom } := by
  refine ⟨(pullbackCongr h).app M, Iso.app_hom _ _, rfl, ?_⟩
  subst k
  simp [pullbackCongr]

/-- Project the checked comparison before any concrete scheme is substituted. -/
def pullbackInclusionComparison {X Y : Scheme.{u}} {j k : X ⟶ Y}
    (h : j = k) (M : Y.Modules)
    (i : M ⟶ (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf)) :
    (Scheme.Modules.pullback j).obj M ≅ (Scheme.Modules.pullback k).obj M :=
  (pullbackInclusionComparisonData h M i).val

private theorem pullbackInclusionComparison_hom {X Y : Scheme.{u}} {j k : X ⟶ Y}
    (h : j = k) (M : Y.Modules)
    (i : M ⟶ (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf)) :
    (pullbackInclusionComparison h M i).hom = (pullbackCongr h).hom.app M :=
  (pullbackInclusionComparisonData h M i).property.1

private theorem pullbackInclusionComparison_eq {X Y : Scheme.{u}} {j k : X ⟶ Y}
    (h : j = k) (M : Y.Modules)
    (i : M ⟶ (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf)) :
    pullbackInclusionComparison h M i = (pullbackCongr h).app M :=
  (pullbackInclusionComparisonData h M i).property.2.1

private theorem pullbackInclusionComparison_inclusion {X Y : Scheme.{u}} {j k : X ⟶ Y}
    (h : j = k) (M : Y.Modules)
    (i : M ⟶ (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf)) :
    (pullbackInclusionComparison h M i).hom ≫
        (Scheme.Modules.pullback k).map i ≫ (pullbackUnitIso k).hom =
      (Scheme.Modules.pullback j).map i ≫ (pullbackUnitIso j).hom :=
  (pullbackInclusionComparisonData h M i).property.2.2

private theorem pullbackFrame_hom_relation
    {S T : Type u} [CommRing S] [CommRing T] (φ : S →+* T)
    {M N : (Spec (.of S)).Modules}
    (e₀ : (show (Spec (.of S)).Modules from
      SheafOfModules.unit (Spec (.of S)).ringCatSheaf) ≅ M)
    (e₁ : (show (Spec (.of S)).Modules from
      SheafOfModules.unit (Spec (.of S)).ringCatSheaf) ≅ N)
    (q : N ⟶ M) (r : S) (t : T) (hφ : φ r = t)
    (h : e₁.hom ≫ q = affineMultiplication S r ≫ e₀.hom) :
    (pullbackFrame (Spec.map (CommRingCat.ofHom φ)) e₁).hom ≫
        (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).map q =
      affineMultiplication T t ≫ (pullbackFrame (Spec.map (CommRingCat.ofHom φ)) e₀).hom := by
  have H := pullbackUnitHom_mul φ r e₀.hom (e₁.hom ≫ q) h
  rw [hφ, CategoryTheory.Functor.map_comp] at H
  rw [pullbackFrame_hom, pullbackFrame_hom]
  exact (Category.assoc (obj := (Spec (.of T)).Modules) _ _ _).trans H

private theorem chartFrameAfterMap_eq_frameAlong
    {R : Type u} [CommRing R] {J : Ideal R} (B : BlowupDatum (affineCenter R J))
    (a : J) (T : Type u) [CommRing T] (φ : affineBlowupAlgebra R J a →+* T) :
    chartFrameAfterMap B a T φ =
      frameAlong (Spec.map (CommRingCat.ofHom φ)) (chartMap B a)
        (idealModule (centreι B)) (chartFrame B a) := rfl

/-- The actual kernel module pulled to the first original raw-overlap map. -/
def firstRawOverlapModule : (Spec (.of (Localization.Away (pairCoordinate a b)))).Modules :=
  (Scheme.Modules.pullback
    (Spec.map (CommRingCat.ofHom (firstOverlapRingMap I a b hI ha hb).toRingHom) ≫
      chartMap (blowupDatum (affineCenter A I)) (firstGenerator I a b hI))).obj
        (idealModule (centreι (blowupDatum (affineCenter A I))))

/-- The original first denominator frame on the actual raw overlap. -/
def firstRawOverlapFrame :
    (show (Spec (.of (Localization.Away (pairCoordinate a b)))).Modules from
      SheafOfModules.unit (Spec (.of (Localization.Away (pairCoordinate a b)))).ringCatSheaf) ≅
        firstRawOverlapModule I a b hI ha hb :=
  chartFrameAfterMap (blowupDatum (affineCenter A I)) (firstGenerator I a b hI)
    (Localization.Away (pairCoordinate a b)) (firstOverlapRingMap I a b hI ha hb).toRingHom

/-- The first forward map is exactly the original native chart-frame map. -/
theorem firstRawOverlapFrame_hom :
    (firstRawOverlapFrame I a b hI ha hb).hom =
      (chartFrameAfterMap (blowupDatum (affineCenter A I)) (firstGenerator I a b hI)
        (Localization.Away (pairCoordinate a b))
        (firstOverlapRingMap I a b hI ha hb).toRingHom).hom := rfl

private theorem firstRawOverlapFrame_eq_frameAlong :
    firstRawOverlapFrame I a b hI ha hb =
      frameAlong
        (Spec.map (CommRingCat.ofHom (firstOverlapRingMap I a b hI ha hb).toRingHom))
        (chartMap (blowupDatum (affineCenter A I)) (firstGenerator I a b hI))
        (idealModule (centreι (blowupDatum (affineCenter A I))))
        (chartFrame (blowupDatum (affineCenter A I)) (firstGenerator I a b hI)) :=
  chartFrameAfterMap_eq_frameAlong _ _ _ _

variable (hb' : IsSMulRegular A b) (ha' : IsSMulRegular (A ⧸ Ideal.span {b}) a)

/-- The actual kernel module pulled to the original opposite raw-overlap map. -/
def secondRawOverlapModule : (Spec (.of (Localization.Away (pairCoordinate a b)))).Modules :=
  (Scheme.Modules.pullback
    (Spec.map (CommRingCat.ofHom (secondOverlapRingMap I a b hI hb' ha').toRingHom) ≫
      chartMap (blowupDatum (affineCenter A I))
        (firstGenerator I b a (Ideal.span_pair_comm.trans hI)))).obj
          (idealModule (centreι (blowupDatum (affineCenter A I))))

/-- The original opposite denominator frame, before any equal-map transport. -/
def secondRawOverlapFrame :
    (show (Spec (.of (Localization.Away (pairCoordinate a b)))).Modules from
      SheafOfModules.unit (Spec (.of (Localization.Away (pairCoordinate a b)))).ringCatSheaf) ≅
        secondRawOverlapModule I a b hI hb' ha' :=
  chartFrameAfterMap (blowupDatum (affineCenter A I))
    (firstGenerator I b a (Ideal.span_pair_comm.trans hI))
    (Localization.Away (pairCoordinate a b)) (secondOverlapRingMap I a b hI hb' ha').toRingHom

/-- The opposite forward map is exactly the original untransported chart frame. -/
theorem secondRawOverlapFrame_hom :
    (secondRawOverlapFrame I a b hI hb' ha').hom =
      (chartFrameAfterMap (blowupDatum (affineCenter A I))
        (firstGenerator I b a (Ideal.span_pair_comm.trans hI))
        (Localization.Away (pairCoordinate a b))
        (secondOverlapRingMap I a b hI hb' ha').toRingHom).hom := rfl

private theorem secondRawOverlapFrame_eq_frameAlong :
    secondRawOverlapFrame I a b hI hb' ha' =
      frameAlong
        (Spec.map (CommRingCat.ofHom (secondOverlapRingMap I a b hI hb' ha').toRingHom))
        (chartMap (blowupDatum (affineCenter A I))
          (firstGenerator I b a (Ideal.span_pair_comm.trans hI)))
        (idealModule (centreι (blowupDatum (affineCenter A I))))
        (chartFrame (blowupDatum (affineCenter A I))
          (firstGenerator I b a (Ideal.span_pair_comm.trans hI))) :=
  chartFrameAfterMap_eq_frameAlong _ _ _ _

/-- The original pulled kernel inclusion followed by the original unit comparison. -/
def firstRawOverlapInclusion : firstRawOverlapModule I a b hI ha hb ⟶
    (show (Spec (.of (Localization.Away (pairCoordinate a b)))).Modules from
      SheafOfModules.unit (Spec (.of (Localization.Away (pairCoordinate a b)))).ringCatSheaf) :=
  (Scheme.Modules.pullback
    (Spec.map (CommRingCat.ofHom (firstOverlapRingMap I a b hI ha hb).toRingHom) ≫
      chartMap (blowupDatum (affineCenter A I)) (firstGenerator I a b hI))).map
        (idealInclusion (centreι (blowupDatum (affineCenter A I)))) ≫
    (pullbackUnitIso
      (Spec.map (CommRingCat.ofHom (firstOverlapRingMap I a b hI ha hb).toRingHom) ≫
        chartMap (blowupDatum (affineCenter A I)) (firstGenerator I a b hI))).hom

/-- The same original pulled kernel inclusion on the opposite raw map. -/
def secondRawOverlapInclusion : secondRawOverlapModule I a b hI hb' ha' ⟶
    (show (Spec (.of (Localization.Away (pairCoordinate a b)))).Modules from
      SheafOfModules.unit (Spec (.of (Localization.Away (pairCoordinate a b)))).ringCatSheaf) :=
  (Scheme.Modules.pullback
    (Spec.map (CommRingCat.ofHom (secondOverlapRingMap I a b hI hb' ha').toRingHom) ≫
      chartMap (blowupDatum (affineCenter A I))
        (firstGenerator I b a (Ideal.span_pair_comm.trans hI)))).map
          (idealInclusion (centreι (blowupDatum (affineCenter A I)))) ≫
    (pullbackUnitIso
      (Spec.map (CommRingCat.ofHom (secondOverlapRingMap I a b hI hb' ha').toRingHom) ≫
        chartMap (blowupDatum (affineCenter A I))
          (firstGenerator I b a (Ideal.span_pair_comm.trans hI)))).hom

/-- The actual chart equality supplies the original native module comparison.
Only its already-projected isomorphism is specialized to the concrete blowup. -/
def rawOverlapFrameComparison :
    secondRawOverlapModule I a b hI hb' ha' ≅ firstRawOverlapModule I a b hI ha hb :=
  pullbackInclusionComparison
    (X := Spec (.of (Localization.Away (pairCoordinate a b)))) (Y := canonicalBlowup I)
    (overlapRingMaps_chart I a b hI ha hb hb' ha').symm
    (idealModule (centreι (blowupDatum (affineCenter A I))))
    (idealInclusion (centreι (blowupDatum (affineCenter A I))))

/-- The whole native comparison is retained, beyond its original forward projection. -/
theorem rawOverlapFrameComparison_eq_pullbackCongr :
    rawOverlapFrameComparison I a b hI ha hb hb' ha' =
      (pullbackCongr (overlapRingMaps_chart I a b hI ha hb hb' ha').symm).app
        (idealModule (centreι (blowupDatum (affineCenter A I)))) :=
  pullbackInclusionComparison_eq
    (X := Spec (.of (Localization.Away (pairCoordinate a b)))) (Y := canonicalBlowup I)
    (overlapRingMaps_chart I a b hI ha hb hb' ha').symm
    (idealModule (centreι (blowupDatum (affineCenter A I))))
    (idealInclusion (centreι (blowupDatum (affineCenter A I))))

/-- Its forward map is the literal native equal-map component. -/
theorem rawOverlapFrameComparison_hom :
    (rawOverlapFrameComparison I a b hI ha hb hb' ha').hom =
      (pullbackCongr (overlapRingMaps_chart I a b hI ha hb hb' ha').symm).hom.app
        (idealModule (centreι (blowupDatum (affineCenter A I)))) := by
  have h := congrArg
    (fun e : secondRawOverlapModule I a b hI hb' ha' ≅
      firstRawOverlapModule I a b hI ha hb => e.hom)
    (rawOverlapFrameComparison_eq_pullbackCongr I a b hI ha hb hb' ha')
  exact h.trans (Iso.app_hom
    (pullbackCongr (overlapRingMaps_chart I a b hI ha hb hb' ha').symm)
    (idealModule (centreι (blowupDatum (affineCenter A I)))))

/-- The first original raw frame retains its actual pulled inclusion and denominator value. -/
theorem firstRawOverlapFrame_inclusion :
    (firstRawOverlapFrame I a b hI ha hb).hom ≫
        (Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (firstOverlapRingMap I a b hI ha hb).toRingHom) ≫
            chartMap (blowupDatum (affineCenter A I)) (firstGenerator I a b hI))).map
              (idealInclusion (centreι (blowupDatum (affineCenter A I)))) ≫
        (pullbackUnitIso
          (Spec.map (CommRingCat.ofHom (firstOverlapRingMap I a b hI ha hb).toRingHom) ≫
            chartMap (blowupDatum (affineCenter A I)) (firstGenerator I a b hI))).hom =
      affineMultiplication (Localization.Away (pairCoordinate a b))
        ((firstOverlapRingMap I a b hI ha hb).toRingHom
          (algebraMap A (affineBlowupAlgebra A I a) a)) := by
  have Hnative := chartFrameAfterMap_inclusion (blowupDatum (affineCenter A I))
    (firstGenerator I a b hI) (Localization.Away (pairCoordinate a b))
    (firstOverlapRingMap I a b hI ha hb).toRingHom
  have H := transportInclusionEquation
    (C := (Spec (.of (Localization.Away (pairCoordinate a b)))).Modules)
    (firstRawOverlapFrame_hom I a b hI ha hb) Hnative
  exact H

/-- The opposite original raw frame retains its actual pulled inclusion and denominator value. -/
theorem secondRawOverlapFrame_inclusion :
    (secondRawOverlapFrame I a b hI hb' ha').hom ≫
        (Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (secondOverlapRingMap I a b hI hb' ha').toRingHom) ≫
            chartMap (blowupDatum (affineCenter A I))
              (firstGenerator I b a (Ideal.span_pair_comm.trans hI)))).map
                (idealInclusion (centreι (blowupDatum (affineCenter A I)))) ≫
        (pullbackUnitIso
          (Spec.map (CommRingCat.ofHom (secondOverlapRingMap I a b hI hb' ha').toRingHom) ≫
            chartMap (blowupDatum (affineCenter A I))
              (firstGenerator I b a (Ideal.span_pair_comm.trans hI)))).hom =
      affineMultiplication (Localization.Away (pairCoordinate a b))
        ((secondOverlapRingMap I a b hI hb' ha').toRingHom
          (algebraMap A (affineBlowupAlgebra A I b) b)) := by
  have Hnative := chartFrameAfterMap_inclusion (blowupDatum (affineCenter A I))
    (firstGenerator I b a (Ideal.span_pair_comm.trans hI))
    (Localization.Away (pairCoordinate a b)) (secondOverlapRingMap I a b hI hb' ha').toRingHom
  have H := transportInclusionEquation
    (C := (Spec (.of (Localization.Away (pairCoordinate a b)))).Modules)
    (secondRawOverlapFrame_hom I a b hI hb' ha') Hnative
  exact H

private theorem overlapRingMaps_denominator_ringHom :
    (secondOverlapRingMap I a b hI hb' ha').toRingHom
        (algebraMap A (affineBlowupAlgebra A I b) b) =
      algebraMap (pairQuotient a b) (Localization.Away (pairCoordinate a b))
          (pairCoordinate a b) *
        (firstOverlapRingMap I a b hI ha hb).toRingHom
          (algebraMap A (affineBlowupAlgebra A I a) a) :=
  algHom_toRingHom_mul (secondOverlapRingMap I a b hI hb' ha')
    (firstOverlapRingMap I a b hI ha hb) _ _ _
    (overlapRingMaps_denominator I a b hI ha hb hb' ha')

private theorem firstRawOverlapInclusion_mono : Mono (firstRawOverlapInclusion I a b hI ha hb) := by
  let B := blowupDatum (affineCenter A I)
  let j := Spec.map (CommRingCat.ofHom (firstOverlapRingMap I a b hI ha hb).toRingHom) ≫
    chartMap B (firstGenerator I a b hI)
  have : IsOpenImmersion j := firstOverlapChartIsOpenImmersion I a b hI ha hb
  have : Mono ((Scheme.Modules.pullback j).map (idealInclusion (centreι B))) :=
    idealInclusion_pullback_mono B j
  exact inferInstanceAs (Mono
    ((Scheme.Modules.pullback j).map (idealInclusion (centreι B)) ≫ (pullbackUnitIso j).hom))

private theorem firstRawOverlapFrame_inclusion_named :
    (firstRawOverlapFrame I a b hI ha hb).hom ≫ firstRawOverlapInclusion I a b hI ha hb =
      affineMultiplication (Localization.Away (pairCoordinate a b))
        ((firstOverlapRingMap I a b hI ha hb).toRingHom
          (algebraMap A (affineBlowupAlgebra A I a) a)) :=
  firstRawOverlapFrame_inclusion I a b hI ha hb

private theorem secondRawOverlapFrame_inclusion_named :
    (secondRawOverlapFrame I a b hI hb' ha').hom ≫ secondRawOverlapInclusion I a b hI hb' ha' =
      affineMultiplication (Localization.Away (pairCoordinate a b))
        ((secondOverlapRingMap I a b hI hb' ha').toRingHom
          (algebraMap A (affineBlowupAlgebra A I b) b)) :=
  secondRawOverlapFrame_inclusion I a b hI hb' ha'

/-- The original equal-map comparison commutes with the original pulled kernel inclusions. -/
theorem rawOverlapFrameComparison_inclusion :
    (rawOverlapFrameComparison I a b hI ha hb hb' ha').hom ≫
        firstRawOverlapInclusion I a b hI ha hb = secondRawOverlapInclusion I a b hI hb' ha' :=
  pullbackInclusionComparison_inclusion
    (X := Spec (.of (Localization.Away (pairCoordinate a b)))) (Y := canonicalBlowup I)
    (overlapRingMaps_chart I a b hI ha hb hb' ha').symm
    (idealModule (centreι (blowupDatum (affineCenter A I))))
    (idealInclusion (centreι (blowupDatum (affineCenter A I))))


private theorem rawOverlapScalars_comp :
    affineMultiplication (Localization.Away (pairCoordinate a b))
        ((secondOverlapRingMap I a b hI hb' ha').toRingHom
          (algebraMap A (affineBlowupAlgebra A I b) b)) =
      affineMultiplication (Localization.Away (pairCoordinate a b))
        (algebraMap (pairQuotient a b) (Localization.Away (pairCoordinate a b))
          (pairCoordinate a b)) ≫
        affineMultiplication (Localization.Away (pairCoordinate a b))
          ((firstOverlapRingMap I a b hI ha hb).toRingHom
            (algebraMap A (affineBlowupAlgebra A I a) a)) :=
  (congrArg (affineMultiplication (Localization.Away (pairCoordinate a b)))
    (overlapRingMaps_denominator_ringHom I a b hI ha hb hb' ha')).trans
      (affineMultiplication_comp (Localization.Away (pairCoordinate a b)) _ _).symm

/-- The original raw denominator frames satisfy the pre-fibre scalar relation. -/
theorem rawOverlapFrames_hom :
    (secondRawOverlapFrame I a b hI hb' ha').hom ≫
        (rawOverlapFrameComparison I a b hI ha hb hb' ha').hom =
      affineMultiplication (Localization.Away (pairCoordinate a b))
        (algebraMap (pairQuotient a b) (Localization.Away (pairCoordinate a b))
          (pairCoordinate a b)) ≫ (firstRawOverlapFrame I a b hI ha hb).hom := by
  have : Mono (firstRawOverlapInclusion I a b hI ha hb) :=
    firstRawOverlapInclusion_mono I a b hI ha hb
  exact scalarFrameEquation
    (C := (Spec (.of (Localization.Away (pairCoordinate a b)))).Modules)
    (firstRawOverlapFrame I a b hI ha hb).hom
    (secondRawOverlapFrame I a b hI hb' ha').hom
    (rawOverlapFrameComparison I a b hI ha hb hb' ha').hom
    (firstRawOverlapInclusion I a b hI ha hb) (secondRawOverlapInclusion I a b hI hb' ha')
    _ _ _ (rawOverlapFrameComparison_inclusion I a b hI ha hb hb' ha')
    (firstRawOverlapFrame_inclusion_named I a b hI ha hb)
    (secondRawOverlapFrame_inclusion_named I a b hI hb' ha')
    (rawOverlapScalars_comp I a b hI ha hb hb' ha')


private theorem rawLaurentCoordinate_value :
    (rawLaurentLift I a b hI ha hb).toRingHom
      (algebraMap (pairQuotient a b) (Localization.Away (pairCoordinate a b))
        (pairCoordinate a b)) = LaurentPolynomial.T 1 :=
  (rawLaurentLift_base I a b hI ha hb (pairCoordinate a b)).trans
    (rawLaurentMap_coordinate I a b hI ha hb)

/-- The two original frames and their equality component have the positive Laurent transition. -/
theorem laurentOverlapFrames_hom :
    (pullbackFrame (Spec.map (CommRingCat.ofHom (rawLaurentLift I a b hI ha hb).toRingHom))
      (secondRawOverlapFrame I a b hI hb' ha')).hom ≫
        (Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (rawLaurentLift I a b hI ha hb).toRingHom))).map
            (rawOverlapFrameComparison I a b hI ha hb hb' ha').hom =
      affineMultiplication (LaurentPolynomial (A ⧸ I)) (LaurentPolynomial.T 1) ≫
        (pullbackFrame (Spec.map (CommRingCat.ofHom (rawLaurentLift I a b hI ha hb).toRingHom))
          (firstRawOverlapFrame I a b hI ha hb)).hom :=
  pullbackFrame_hom_relation (rawLaurentLift I a b hI ha hb).toRingHom
    (firstRawOverlapFrame I a b hI ha hb) (secondRawOverlapFrame I a b hI hb' ha')
    (rawOverlapFrameComparison I a b hI ha hb hb' ha').hom
    (algebraMap (pairQuotient a b) (Localization.Away (pairCoordinate a b)) (pairCoordinate a b))
    (LaurentPolynomial.T 1) (rawLaurentCoordinate_value I a b hI ha hb)
    (rawOverlapFrames_hom I a b hI ha hb hb' ha')

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible IdealFrames Scheme.PolynomialLaurent

variable {A : Type u} [CommRing A] (I : Ideal A) (a b : A)
  (hI : Ideal.span {a, b} = I) (ha : IsSMulRegular A a)
  (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)

/-- Recombining the actual conormal frame with its inclusion gives the original ideal frame. -/
theorem conormalChartFrame_total :
    conormalChartFrame I a b hI ha hb ≪≫
        (pullbackComp (centreChart I a b hI ha hb)
          ((affineCenter A I).comap (blowdown I)).subschemeι).app (centreIdealLine I).val =
      reducedIdealFrame I a b hI ha hb ≪≫
        ((pullbackCongr (centreChart_ι I a b hI ha hb)).app (centreIdealLine I).val).symm := by
  apply Iso.ext
  simp only [conormalChartFrame, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

private theorem conormalChartFrame_total_native :
    conormalChartFrame I a b hI ha hb ≪≫
        (pullbackComp (centreChart I a b hI ha hb)
          ((affineCenter A I).comap (blowdown I)).subschemeι).app (centreIdealLine I).val =
      reducedIdealFrame I a b hI ha hb ≪≫
        (pullbackCongr (centreChart_ι I a b hI ha hb).symm).app (centreIdealLine I).val :=
  (conormalChartFrame_total I a b hI ha hb).trans
    (congrArg (fun q => reducedIdealFrame I a b hI ha hb ≪≫ q)
      (pullbackCongr_symm_app (centreChart_ι I a b hI ha hb) (centreIdealLine I).val))

/-- Further chart pullback of the actual conormal frame retains both original total-map
comparisons. No cancellation of the ideal inclusion on the fibre is used. -/
theorem conormalFrameAlong_total {W : Scheme.{u}}
    (p : W ⟶ Spec (.of (Polynomial (A ⧸ I)))) :
    frameAlong p (centreChart I a b hI ha hb) (centreConormalLine I).val
        (conormalChartFrame I a b hI ha hb) ≪≫
        (pullbackComp (p ≫ centreChart I a b hI ha hb)
          ((affineCenter A I).comap (blowdown I)).subschemeι).app (centreIdealLine I).val =
      frameAlong p (chartFibreToBlowup I a b hI ha hb) (centreIdealLine I).val
        (reducedIdealFrame I a b hI ha hb) ≪≫
        (pullbackCongr (congrArg (fun q => p ≫ q)
          (centreChart_ι I a b hI ha hb).symm)).app (centreIdealLine I).val ≪≫
        (pullbackCongr (Category.assoc p (centreChart I a b hI ha hb)
          ((affineCenter A I).comap (blowdown I)).subschemeι).symm).app
            (centreIdealLine I).val := by
  change frameAlong p (centreChart I a b hI ha hb)
      ((Scheme.Modules.pullback ((affineCenter A I).comap (blowdown I)).subschemeι).obj
        (centreIdealLine I).val) (conormalChartFrame I a b hI ha hb) ≪≫
      (pullbackComp (p ≫ centreChart I a b hI ha hb)
        ((affineCenter A I).comap (blowdown I)).subschemeι).app (centreIdealLine I).val = _
  rw [frameAlong_postcomp, conormalChartFrame_total]
  rw [pullbackCongr_symm_app, frameAlong_congr_right]
  exact Iso.trans_assoc _ _ _

variable (hb' : IsSMulRegular A b) (ha' : IsSMulRegular (A ⧸ Ideal.span {b}) a)

/-- The original positive and inverse Laurent centre-chart maps agree. -/
theorem centreCharts_laurent_compatibility :
    laurentPlus (.of (A ⧸ I)) ≫ centreChart I a b hI ha hb =
      laurentMinus (.of (A ⧸ I)) ≫
        centreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha' := by
  simp only [centreChart, ← Category.assoc]
  rw [fibreCharts_laurent_compatibility]

/-- The original Laurent source is exactly the overlap of the actual centre charts. -/
theorem centreCharts_isPullback :
    IsPullback (laurentPlus (.of (A ⧸ I))) (laurentMinus (.of (A ⧸ I)))
      (centreChart I a b hI ha hb)
      (centreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha') := by
  apply (IsOpenImmersion.isPullback _ _ _ _
    (centreCharts_laurent_compatibility I a b hI ha hb hb' ha') ?_).flip
  ext x
  change (∃ y, (fibreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha' ≫
      (centreFibreIso I).inv) y =
    (fibreChart I a b hI ha hb ≫ (centreFibreIso I).inv) x) ↔ _
  have he : (∃ y, (fibreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha' ≫
      (centreFibreIso I).inv) y =
    (fibreChart I a b hI ha hb ≫ (centreFibreIso I).inv) x) ↔
      x ∈ fibreChart I a b hI ha hb ⁻¹ᵁ
        (fibreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha').opensRange := by
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, (centreFibreIso I).inv.homeomorph.injective hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, congrArg (fun z => (centreFibreIso I).inv z) hy⟩
  rw [he, fibreChart_preimage_other]
  rfl

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory AlgebraicGeometry Scheme.Modules Scheme.Modules.Invertible IdealFrames
open Scheme.PolynomialLaurent

variable {A : Type u} [CommRing A] (I : Ideal A) (a b : A)
  (hI : Ideal.span {a, b} = I) (ha : IsSMulRegular A a)
  (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)

/-- The first Laurent reduction square keeps the original saturated-chart map. -/
theorem laurentPlus_chartReduction_square :
    laurentPlus (.of (A ⧸ I)) ≫
        Spec.map (CommRingCat.ofHom (chartFibreRingMap I a b hI ha hb).toRingHom) =
      Spec.map (CommRingCat.ofHom (rawLaurentLift I a b hI ha hb).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (firstOverlapRingMap I a b hI ha hb).toRingHom) := by
  rw [laurentPlus, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact congrArg (fun f : affineBlowupAlgebra A I a →ₐ[A] LaurentPolynomial (A ⧸ I) =>
    CommRingCat.ofHom f.toRingHom) (firstOverlapRingMap_laurent I a b hI ha hb).symm

variable (hb' : IsSMulRegular A b) (ha' : IsSMulRegular (A ⧸ Ideal.span {b}) a)

/-- The second Laurent reduction square keeps the original reciprocal saturated-chart map. -/
theorem laurentMinus_chartReduction_square :
    laurentMinus (.of (A ⧸ I)) ≫
        Spec.map (CommRingCat.ofHom
          (chartFibreRingMap I b a (Ideal.span_pair_comm.trans hI) hb' ha').toRingHom) =
      Spec.map (CommRingCat.ofHom (rawLaurentLift I a b hI ha hb).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (secondOverlapRingMap I a b hI hb' ha').toRingHom) := by
  rw [laurentMinus, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact congrArg (fun f : affineBlowupAlgebra A I b →ₐ[A] LaurentPolynomial (A ⧸ I) =>
    CommRingCat.ofHom f.toRingHom) (secondOverlapRingMap_laurent I a b hI ha hb hb' ha').symm

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory AlgebraicGeometry Scheme.Modules Scheme.Modules.Invertible IdealFrames
open Scheme.PolynomialLaurent Localization.Away

private theorem frameAlong_ambient_transition
    {W P₀ P₁ O S₀ S₁ E X : Scheme.{u}}
    (p₀ : W ⟶ P₀) (p₁ : W ⟶ P₁) (δ₀ : P₀ ⟶ S₀) (δ₁ : P₁ ⟶ S₁)
    (l : W ⟶ O) (r₀ : O ⟶ S₀) (r₁ : O ⟶ S₁)
    (c₀ : P₀ ⟶ E) (c₁ : P₁ ⟶ E) (i : E ⟶ X) (j₀ : S₀ ⟶ X) (j₁ : S₁ ⟶ X)
    (hs₀ : p₀ ≫ δ₀ = l ≫ r₀) (hs₁ : p₁ ≫ δ₁ = l ≫ r₁)
    (hc₀ : c₀ ≫ i = δ₀ ≫ j₀) (hc₁ : c₁ ≫ i = δ₁ ≫ j₁)
    (hq : p₀ ≫ c₀ = p₁ ≫ c₁) (hr : r₀ ≫ j₀ = r₁ ≫ j₁)
    (M : X.Modules)
    (e₀ : SheafOfModules.unit S₀.ringCatSheaf ≅ (Scheme.Modules.pullback j₀).obj M)
    (e₁ : SheafOfModules.unit S₁.ringCatSheaf ≅ (Scheme.Modules.pullback j₁).obj M)
    (d₀ : SheafOfModules.unit P₀.ringCatSheaf ≅
      (Scheme.Modules.pullback c₀).obj ((Scheme.Modules.pullback i).obj M))
    (d₁ : SheafOfModules.unit P₁.ringCatSheaf ≅
      (Scheme.Modules.pullback c₁).obj ((Scheme.Modules.pullback i).obj M))
    (hd₀ : d₀ ≪≫ (pullbackComp c₀ i).app M =
      frameAlong δ₀ j₀ M e₀ ≪≫ (pullbackCongr hc₀.symm).app M)
    (hd₁ : d₁ ≪≫ (pullbackComp c₁ i).app M =
      frameAlong δ₁ j₁ M e₁ ≪≫ (pullbackCongr hc₁.symm).app M)
    (R₀ : SheafOfModules.unit O.ringCatSheaf ≅
      (Scheme.Modules.pullback (r₀ ≫ j₀)).obj M)
    (R₁ : SheafOfModules.unit O.ringCatSheaf ≅
      (Scheme.Modules.pullback (r₁ ≫ j₁)).obj M)
    (hR₀ : R₀ = frameAlong r₀ j₀ M e₀) (hR₁ : R₁ = frameAlong r₁ j₁ M e₁)
    (Q : (Scheme.Modules.pullback (r₁ ≫ j₁)).obj M ≅
      (Scheme.Modules.pullback (r₀ ≫ j₀)).obj M)
    (hQ : Q = (pullbackCongr hr.symm).app M)
    (s : (show W.Modules from SheafOfModules.unit W.ringCatSheaf) ⟶
      SheafOfModules.unit W.ringCatSheaf)
    (Hraw : (pullbackFrame l R₁).hom ≫
        (Scheme.Modules.pullback l).map Q.hom =
      s ≫ (pullbackFrame l R₀).hom) :
    (frameAlong p₁ c₁ ((Scheme.Modules.pullback i).obj M) d₁).hom ≫
        (pullbackCongr hq.symm).hom.app ((Scheme.Modules.pullback i).obj M) =
      s ≫ (frameAlong p₀ c₀ ((Scheme.Modules.pullback i).obj M) d₀).hom := by
  rw [hR₀, hR₁, hQ] at Hraw
  let h₀ := frameSquareTotalEq p₀ δ₀ l r₀ c₀ i j₀ hs₀ hc₀
  let h₁ := frameSquareTotalEq p₁ δ₁ l r₁ c₁ i j₁ hs₁ hc₁
  let C₀ := (pullbackComp (p₀ ≫ c₀) i).app M ≪≫ (pullbackCongr h₀).app M ≪≫
    ((pullbackComp l (r₀ ≫ j₀)).app M).symm
  let C₁ := (pullbackComp (p₁ ≫ c₁) i).app M ≪≫ (pullbackCongr h₁).app M ≪≫
    ((pullbackComp l (r₁ ≫ j₁)).app M).symm
  have H := transportFrame_hom
    (frameAlong p₀ c₀ ((Scheme.Modules.pullback i).obj M) d₀)
    (frameAlong p₁ c₁ ((Scheme.Modules.pullback i).obj M) d₁)
    ((pullbackCongr hq.symm).app ((Scheme.Modules.pullback i).obj M))
    C₀ C₁ (pullbackFrame l (frameAlong r₀ j₀ M e₀))
    (pullbackFrame l (frameAlong r₁ j₁ M e₁))
    ((Scheme.Modules.pullback l).mapIso ((pullbackCongr hr.symm).app M)) s
    (frameAlong_ambient_square p₀ δ₀ l r₀ c₀ i j₀ hs₀ hc₀ M e₀ d₀ hd₀)
    (frameAlong_ambient_square p₁ δ₁ l r₁ c₁ i j₁ hs₁ hc₁ M e₁ d₁ hd₁)
    (ambientComparison_congr l i hq.symm hr.symm h₀ h₁ M) Hraw
  exact H

variable {A : Type u} [CommRing A] (I : Ideal A) (a b : A)
  (hI : Ideal.span {a, b} = I) (ha : IsSMulRegular A a)
  (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)

/-- The first conormal frame restricted to the original Laurent overlap map. -/
def firstConormalLaurentFrame :=
  frameAlong (laurentPlus (.of (A ⧸ I))) (centreChart I a b hI ha hb)
    (centreConormalLine I).val (conormalChartFrame I a b hI ha hb)

variable (hb' : IsSMulRegular A b) (ha' : IsSMulRegular (A ⧸ Ideal.span {b}) a)

/-- The original conormal generators have the literal positive Laurent transition.
The pre-fibre ideal inclusion was cancelled only in the already-proved raw transition;
this proof cancels only native isomorphisms of actual pullback modules. -/
theorem conormalLaurentFrames_transition :
    (frameAlong (laurentMinus (.of (A ⧸ I)))
      (centreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha')
      ((Scheme.Modules.pullback ((affineCenter A I).comap (blowdown I)).subschemeι).obj
        (centreIdealLine I).val)
      (conormalChartFrame I b a (Ideal.span_pair_comm.trans hI) hb' ha')).hom ≫
        (pullbackCongr (centreCharts_laurent_compatibility I a b hI ha hb hb' ha').symm).hom.app
          ((Scheme.Modules.pullback ((affineCenter A I).comap (blowdown I)).subschemeι).obj
            (centreIdealLine I).val) =
      affineMultiplication (LaurentPolynomial (A ⧸ I)) (LaurentPolynomial.T 1) ≫
        (frameAlong (laurentPlus (.of (A ⧸ I))) (centreChart I a b hI ha hb)
          ((Scheme.Modules.pullback ((affineCenter A I).comap (blowdown I)).subschemeι).obj
            (centreIdealLine I).val) (conormalChartFrame I a b hI ha hb)).hom := by
  have H := frameAlong_ambient_transition
    (laurentPlus (.of (A ⧸ I))) (laurentMinus (.of (A ⧸ I)))
    (Spec.map (CommRingCat.ofHom (chartFibreRingMap I a b hI ha hb).toRingHom))
    (Spec.map (CommRingCat.ofHom
      (chartFibreRingMap I b a (Ideal.span_pair_comm.trans hI) hb' ha').toRingHom))
    (Spec.map (CommRingCat.ofHom (rawLaurentLift I a b hI ha hb).toRingHom))
    (Spec.map (CommRingCat.ofHom (firstOverlapRingMap I a b hI ha hb).toRingHom))
    (Spec.map (CommRingCat.ofHom (secondOverlapRingMap I a b hI hb' ha').toRingHom))
    (centreChart I a b hI ha hb)
    (centreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha')
    ((affineCenter A I).comap (blowdown I)).subschemeι
    (chartMap (blowupDatum (affineCenter A I)) (firstGenerator I a b hI))
    (chartMap (blowupDatum (affineCenter A I))
      (firstGenerator I b a (Ideal.span_pair_comm.trans hI)))
    (laurentPlus_chartReduction_square I a b hI ha hb)
    (laurentMinus_chartReduction_square I a b hI ha hb hb' ha')
    (centreChart_ι I a b hI ha hb)
    (centreChart_ι I b a (Ideal.span_pair_comm.trans hI) hb' ha')
    (centreCharts_laurent_compatibility I a b hI ha hb hb' ha')
    (overlapRingMaps_chart I a b hI ha hb hb' ha')
    (centreIdealLine I).val
    (chartFrame (blowupDatum (affineCenter A I)) (firstGenerator I a b hI))
    (chartFrame (blowupDatum (affineCenter A I))
      (firstGenerator I b a (Ideal.span_pair_comm.trans hI)))
    (conormalChartFrame I a b hI ha hb)
    (conormalChartFrame I b a (Ideal.span_pair_comm.trans hI) hb' ha')
    (conormalChartFrame_total_native I a b hI ha hb)
    (conormalChartFrame_total_native I b a (Ideal.span_pair_comm.trans hI) hb' ha')
    (firstRawOverlapFrame I a b hI ha hb) (secondRawOverlapFrame I a b hI hb' ha')
    (firstRawOverlapFrame_eq_frameAlong I a b hI ha hb)
    (secondRawOverlapFrame_eq_frameAlong I a b hI hb' ha')
    (rawOverlapFrameComparison I a b hI ha hb hb' ha')
    (rawOverlapFrameComparison_eq_pullbackCongr I a b hI ha hb hb' ha')
    (affineMultiplication (LaurentPolynomial (A ⧸ I)) (LaurentPolynomial.T 1))
    (laurentOverlapFrames_hom I a b hI ha hb hb' ha')
  exact H

end AlgebraicGeometry.Scheme.Blowup.RegularPoint
