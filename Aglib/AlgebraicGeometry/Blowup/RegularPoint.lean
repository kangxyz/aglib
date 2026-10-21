/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Charts
public import Aglib.AlgebraicGeometry.Spec.ResidueFiber

/-!
# The actual exceptional projective line of a regular local surface

Regular parameters are supplied from the original local ring and its exact
dimension. The constructed universal blowup has the original residue fibre,
and its two actual polynomial charts give an isomorphism over the original
residue field with the native homogeneous projective line.

The actual normal-line comparison is a further geometric obligation.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

variable (A : Type u) [CommRing A] [IsRegularLocalRing A] (hd : ringKrullDim A = 2)

/-- An actual first parameter supplied by the regular-local dimension theorem. -/
def firstParameter : A := (IsRegularLocalRing.exists_regularPair A hd).choose

/-- The actual lifted second parameter from the same supplied pair. -/
def secondParameter : A := (IsRegularLocalRing.exists_regularPair A hd).choose_spec.choose

/-- The chosen parameters generate the actual maximal ideal and are regular in both orders. -/
theorem parameters_spec :
    firstParameter A hd ∈ maximalIdeal A ∧ secondParameter A hd ∈ maximalIdeal A ∧
      Ideal.span {firstParameter A hd, secondParameter A hd} = maximalIdeal A ∧
      IsSMulRegular A (firstParameter A hd) ∧
      IsSMulRegular (A ⧸ Ideal.span {firstParameter A hd}) (secondParameter A hd) ∧
      IsSMulRegular A (secondParameter A hd) ∧
      IsSMulRegular (A ⧸ Ideal.span {secondParameter A hd}) (firstParameter A hd) :=
  (IsRegularLocalRing.exists_regularPair A hd).choose_spec.choose_spec

/-- The actual first polynomial chart of the closed-point fibre of the constructed blowup. -/
def firstFibreChart : Spec (.of (Polynomial (ResidueField A))) ⟶
    pullback (blowupDatum (affineCenter A (maximalIdeal A))).map (LocalRing.residueSpecMap A) :=
  fibreChart (maximalIdeal A) (firstParameter A hd) (secondParameter A hd)
    (parameters_spec A hd).2.2.1 (parameters_spec A hd).2.2.2.1
    (parameters_spec A hd).2.2.2.2.1

/-- The actual opposite polynomial chart, over the same original residue field. -/
def secondFibreChart : Spec (.of (Polynomial (ResidueField A))) ⟶
    pullback (blowupDatum (affineCenter A (maximalIdeal A))).map (LocalRing.residueSpecMap A) :=
  fibreChart (maximalIdeal A) (secondParameter A hd) (firstParameter A hd)
    (Ideal.span_pair_comm.trans (parameters_spec A hd).2.2.1)
    (parameters_spec A hd).2.2.2.2.2.1 (parameters_spec A hd).2.2.2.2.2.2

/-- The original two-chart pushout identifies with the literal residue fibre. -/
def parameterExceptionalOverIso :
    Over.mk (ProjectiveLine.TwoChart.projection (.of (ResidueField A))) ≅
      Over.mk (pullback.snd (blowupDatum (affineCenter A (maximalIdeal A))).map
        (LocalRing.residueSpecMap A)) :=
  twoChartExceptionalOverIso (maximalIdeal A) (firstParameter A hd) (secondParameter A hd)
    (parameters_spec A hd).2.2.1 (parameters_spec A hd).2.2.2.1
    (parameters_spec A hd).2.2.2.2.1 (parameters_spec A hd).2.2.2.2.2.1
    (parameters_spec A hd).2.2.2.2.2.2

/-- The actual closed-point fibre of the actual constructed blowup is the native projective
line over its original residue field. No exceptional-curve or blowup-model premise is supplied. -/
def exceptionalOverIsoProjectiveP1 :
    Over.mk (pullback.snd (blowupDatum (affineCenter A (maximalIdeal A))).map
      (LocalRing.residueSpecMap A)) ≅
      Over.mk (ProjectiveLine.structureMap (ResidueField A)) :=
  (parameterExceptionalOverIso A hd).symm ≪≫
    ProjectiveLine.TwoChart.twoChartLineOverIsoProjectiveP1 (ResidueField A)

/-- The forward map retains the original literal residue-fibre projection. -/
@[reassoc]
theorem exceptionalOverIsoProjectiveP1_hom_over :
    (exceptionalOverIsoProjectiveP1 A hd).hom.left ≫
        ProjectiveLine.structureMap (ResidueField A) =
      pullback.snd (blowupDatum (affineCenter A (maximalIdeal A))).map
        (LocalRing.residueSpecMap A) :=
  (exceptionalOverIsoProjectiveP1 A hd).hom.w

/-- The first original parameter chart is exactly the standard zero chart of native P1. -/
@[reassoc]
theorem firstFibreChart_projectiveP1 :
    firstFibreChart A hd ≫ (exceptionalOverIsoProjectiveP1 A hd).hom.left =
      ProjectiveLine.chart (ResidueField A) 0 := by
  let e := twoChartExceptionalIso (maximalIdeal A) (firstParameter A hd) (secondParameter A hd)
    (parameters_spec A hd).2.2.1 (parameters_spec A hd).2.2.2.1
    (parameters_spec A hd).2.2.2.2.1 (parameters_spec A hd).2.2.2.2.2.1
    (parameters_spec A hd).2.2.2.2.2.2
  have he : ProjectiveLine.TwoChart.plusChart (.of (ResidueField A)) ≫ e.hom =
      firstFibreChart A hd :=
    twoChartExceptionalIso_plus (maximalIdeal A) (firstParameter A hd) (secondParameter A hd)
      (parameters_spec A hd).2.2.1 (parameters_spec A hd).2.2.2.1
      (parameters_spec A hd).2.2.2.2.1 (parameters_spec A hd).2.2.2.2.2.1
      (parameters_spec A hd).2.2.2.2.2.2
  change firstFibreChart A hd ≫
    (e.inv ≫ (ProjectiveLine.TwoChart.twoChartLineIsoProjectiveP1 (ResidueField A)).hom) = _
  rw [← he, Category.assoc, Iso.hom_inv_id_assoc,
    ProjectiveLine.TwoChart.twoChartLineIsoProjectiveP1_plusChart]

/-- The opposite parameter chart is exactly the standard one chart of the same native P1. -/
@[reassoc]
theorem secondFibreChart_projectiveP1 :
    secondFibreChart A hd ≫ (exceptionalOverIsoProjectiveP1 A hd).hom.left =
      ProjectiveLine.chart (ResidueField A) 1 := by
  let e := twoChartExceptionalIso (maximalIdeal A) (firstParameter A hd) (secondParameter A hd)
    (parameters_spec A hd).2.2.1 (parameters_spec A hd).2.2.2.1
    (parameters_spec A hd).2.2.2.2.1 (parameters_spec A hd).2.2.2.2.2.1
    (parameters_spec A hd).2.2.2.2.2.2
  have he : ProjectiveLine.TwoChart.minusChart (.of (ResidueField A)) ≫ e.hom =
      secondFibreChart A hd :=
    twoChartExceptionalIso_minus (maximalIdeal A) (firstParameter A hd) (secondParameter A hd)
      (parameters_spec A hd).2.2.1 (parameters_spec A hd).2.2.2.1
      (parameters_spec A hd).2.2.2.2.1 (parameters_spec A hd).2.2.2.2.2.1
      (parameters_spec A hd).2.2.2.2.2.2
  change secondFibreChart A hd ≫
    (e.inv ≫ (ProjectiveLine.TwoChart.twoChartLineIsoProjectiveP1 (ResidueField A)).hom) = _
  rw [← he, Category.assoc, Iso.hom_inv_id_assoc,
    ProjectiveLine.TwoChart.twoChartLineIsoProjectiveP1_minusChart]

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
variable {A : Type u} [CommRing A] (I : Ideal A)

instance quotientImmersionIsClosedImmersion : IsClosedImmersion (quotientImmersion I) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The original quotient scheme is the actual ideal-sheaf centre. -/
def quotientCentreIso : Spec (.of (A ⧸ I)) ≅ (affineCenter A I).subscheme :=
  asIso (quotientImmersion I).toImage

@[reassoc (attr := simp)]
theorem quotientCentreIso_hom_ι :
    (quotientCentreIso I).hom ≫ (affineCenter A I).subschemeι = quotientImmersion I :=
  (quotientImmersion I).toImage_imageι

/-- The actual residue fibre remains Cartesian over the original ideal-sheaf centre. -/
theorem centrePullbackSquare :
    IsPullback (exceptionalι I)
      (exceptionalStructureMap I ≫ (quotientCentreIso I).hom)
      (blowdown I) (affineCenter A I).subschemeι := by
  apply (IsPullback.of_hasPullback (blowdown I) (quotientImmersion I)).of_iso
    (Iso.refl _) (Iso.refl _) (quotientCentreIso I) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, quotientCentreIso_hom_ι]

/-- The actual inverse-image-centre subscheme is canonically the original quotient fibre. -/
def centreFibreIso : ((affineCenter A I).comap (blowdown I)).subscheme ≅ exceptionalFibre I :=
  (affineCenter A I).comapIso (blowdown I) ≪≫ (centrePullbackSquare I).isoPullback.symm

@[reassoc (attr := simp)]
theorem centreFibreIso_hom_ι :
    (centreFibreIso I).hom ≫ exceptionalι I =
      ((affineCenter A I).comap (blowdown I)).subschemeι := by
  have ht : (centrePullbackSquare I).isoPullback.inv ≫ exceptionalι I =
      pullback.fst (blowdown I) (affineCenter A I).subschemeι := by
    apply (cancel_epi (centrePullbackSquare I).isoPullback.hom).mp
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact (centrePullbackSquare I).isoPullback_hom_fst.symm
  simp only [centreFibreIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [ht, Scheme.IdealSheafData.comapIso_hom_fst]

/-- The actual inverse-image centre retains its original quotient structural arrow. -/
def centreStructureMap : ((affineCenter A I).comap (blowdown I)).subscheme ⟶ Spec (.of (A ⧸ I)) :=
  (centreFibreIso I).hom ≫ exceptionalStructureMap I

@[reassoc]
theorem centreStructureMap_immersion :
    centreStructureMap I ≫ quotientImmersion I =
      ((affineCenter A I).comap (blowdown I)).subschemeι ≫ blowdown I := by
  rw [centreStructureMap, Category.assoc, ← pullback.condition,
    ← Category.assoc, centreFibreIso_hom_ι]

/-- The centre comparison is over the original quotient spectrum. -/
def centreFibreOverIso : Over.mk (centreStructureMap I) ≅ Over.mk (exceptionalStructureMap I) :=
  Over.isoMk (centreFibreIso I) rfl

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
variable (A : Type u) [CommRing A] [IsRegularLocalRing A] (hd : ringKrullDim A = 2)

/-- The actual inverse-image-centre subscheme of the regular-point blowup is native P1,
over the same original residue field as the literal fibre. -/
def centreOverIsoProjectiveP1 :
    Over.mk (centreStructureMap (maximalIdeal A)) ≅
      Over.mk (ProjectiveLine.structureMap (ResidueField A)) :=
  centreFibreOverIso (maximalIdeal A) ≪≫ exceptionalOverIsoProjectiveP1 A hd

@[reassoc]
theorem centreOverIsoProjectiveP1_hom_over :
    (centreOverIsoProjectiveP1 A hd).hom.left ≫ ProjectiveLine.structureMap (ResidueField A) =
      centreStructureMap (maximalIdeal A) :=
  (centreOverIsoProjectiveP1 A hd).hom.w

end AlgebraicGeometry.Scheme.Blowup.RegularPoint
