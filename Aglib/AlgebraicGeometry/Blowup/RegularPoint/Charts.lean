/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Blowup.RegularPair.Reciprocal
public import Aglib.AlgebraicGeometry.Blowup.Construction
public import Aglib.AlgebraicGeometry.Blowup.GeneratorAtlas
public import Aglib.AlgebraicGeometry.Limits.Range
public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Comparison

/-!
# Actual exceptional-fibre charts of a regular pair

The polynomial fibre charts map to the literal fibre product of the constructed
blowup and the original quotient centre. Their Cartesian squares retain the
original saturated atlas maps, quotient homomorphisms, and both projections.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open Localization.Away Scheme.PolynomialLaurent

variable {A : Type u} [CommRing A]

/-- The already constructed universal blowup, with its actual ideal centre. -/
abbrev canonicalBlowup (I : Ideal A) : Scheme.{u} :=
  (blowupDatum (affineCenter A I)).Y

/-- The structural arrow of that same constructed blowup. -/
abbrev blowdown (I : Ideal A) : canonicalBlowup I ⟶ Spec (.of A) :=
  (blowupDatum (affineCenter A I)).map

/-- The original affine quotient immersion. -/
def quotientImmersion (I : Ideal A) : Spec (.of (A ⧸ I)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- The literal residue fibre of the actual blowdown. -/
abbrev exceptionalFibre (I : Ideal A) : Scheme.{u} :=
  pullback (blowdown I) (quotientImmersion I)

/-- The first projection is the actual exceptional closed immersion. -/
abbrev exceptionalι (I : Ideal A) : exceptionalFibre I ⟶ canonicalBlowup I :=
  pullback.fst (blowdown I) (quotientImmersion I)

/-- The second projection retains the original quotient coefficient scheme. -/
abbrev exceptionalStructureMap (I : Ideal A) : exceptionalFibre I ⟶ Spec (.of (A ⧸ I)) :=
  pullback.snd (blowdown I) (quotientImmersion I)

variable (I : Ideal A) (a b : A) (hI : Ideal.span {a, b} = I)
  (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)

/-- The original first parameter as an actual element of the centre ideal. -/
def firstGenerator : I := ⟨a, hI ▸ Ideal.subset_span (by simp)⟩

/-- The polynomial identification of the actual saturated-chart fibre ring. -/
def chartFibreEquiv :
    (affineBlowupAlgebra A I a ⧸ I.map (algebraMap A (affineBlowupAlgebra A I a))) ≃ₐ[A]
      (A ⧸ I)[X] := by
  subst I
  exact pairChartFibreEquiv a b ha hb

/-- The actual chart-ring reduction, followed by its proved polynomial comparison. -/
def chartFibreRingMap : affineBlowupAlgebra A I a →ₐ[A] (A ⧸ I)[X] :=
  (chartFibreEquiv I a b hI ha hb).toAlgHom.comp (Ideal.Quotient.mkₐ A _)

/-- The ring map preserves the original coefficient quotient. -/
theorem chartFibreRingMap_base (r : A) :
    chartFibreRingMap I a b hI ha hb (algebraMap A (affineBlowupAlgebra A I a) r) =
      C (Ideal.Quotient.mk I r) :=
  (chartFibreRingMap I a b hI ha hb).commutes r

private theorem specQuotientPolynomialSquare (I : Ideal A) (S : Type u)
    [CommRing S] [Algebra A S]
    (eR : (S ⧸ I.map (algebraMap A S)) ≃ₐ[A] (A ⧸ I)[X]) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (eR.toAlgHom.comp (Ideal.Quotient.mkₐ A (I.map (algebraMap A S)))).toRingHom))
      (polynomialProjection (.of (A ⧸ I)))
      (Spec.map (CommRingCat.ofHom (algebraMap A S))) (quotientImmersion I) := by
  let J := I.map (algebraMap A S)
  let e : Spec (.of (A ⧸ I)[X]) ≅ Spec (.of (S ⧸ J)) :=
    Scheme.Spec.mapIso eR.toRingEquiv.toCommRingCatIso.op
  have H := isPullback_SpecMap_of_isPushout _ _ _ _
    (BaseChange.quotient_isPushout (algebraMap A S) I)
  apply H.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · change Spec.map (CommRingCat.ofHom eR.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) =
      Spec.map (CommRingCat.ofHom
        (eR.toAlgHom.comp (Ideal.Quotient.mkₐ A J)).toRingHom) ≫ 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp]
    rfl
  · change Spec.map (CommRingCat.ofHom eR.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap J (algebraMap A S) Ideal.le_comap_map)) =
      polynomialProjection (.of (A ⧸ I)) ≫ 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro r
    exact eR.commutes r
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ 𝟙 _ =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
    simp only [Category.id_comp, Category.comp_id]

/-- The polynomial chart square is the original affine quotient pullback square. -/
theorem chartFibreSquare :
    IsPullback (Spec.map (CommRingCat.ofHom (chartFibreRingMap I a b hI ha hb).toRingHom))
      (polynomialProjection (.of (A ⧸ I))) (affineChartMap A I a) (quotientImmersion I) :=
  specQuotientPolynomialSquare I (affineBlowupAlgebra A I a) (chartFibreEquiv I a b hI ha hb)

/-- The original polynomial fibre chart maps into the original saturated blowup chart. -/
def chartFibreToBlowup : Spec (.of (A ⧸ I)[X]) ⟶ canonicalBlowup I :=
  Spec.map (CommRingCat.ofHom (chartFibreRingMap I a b hI ha hb).toRingHom) ≫
    (affineAtlas (blowupDatum (affineCenter A I))).chart (firstGenerator I a b hI)

/-- The polynomial fibre chart retains the original blowdown triangle. -/
theorem chartFibreToBlowup_base :
    chartFibreToBlowup I a b hI ha hb ≫ blowdown I =
      polynomialProjection (.of (A ⧸ I)) ≫ quotientImmersion I := by
  rw [chartFibreToBlowup, Category.assoc,
    (affineAtlas (blowupDatum (affineCenter A I))).triangle]
  exact (chartFibreSquare I a b hI ha hb).w

/-- The polynomial chart in the literal fibre product, defined by its two original projections. -/
def fibreChart : Spec (.of (A ⧸ I)[X]) ⟶ exceptionalFibre I :=
  pullback.lift (chartFibreToBlowup I a b hI ha hb) (polynomialProjection (.of (A ⧸ I)))
    (chartFibreToBlowup_base I a b hI ha hb)

@[reassoc (attr := simp)]
theorem fibreChart_fst :
    fibreChart I a b hI ha hb ≫ exceptionalι I = chartFibreToBlowup I a b hI ha hb :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fibreChart_snd :
    fibreChart I a b hI ha hb ≫ exceptionalStructureMap I =
      polynomialProjection (.of (A ⧸ I)) :=
  pullback.lift_snd _ _ _

/-- The displayed polynomial fibre chart is the actual pullback of the original atlas chart. -/
theorem fibreChart_isPullback :
    IsPullback (fibreChart I a b hI ha hb)
      (Spec.map (CommRingCat.ofHom (chartFibreRingMap I a b hI ha hb).toRingHom))
      (exceptionalι I)
      ((affineAtlas (blowupDatum (affineCenter A I))).chart (firstGenerator I a b hI)) := by
  have H : IsPullback
      (fibreChart I a b hI ha hb ≫ exceptionalStructureMap I)
      (Spec.map (CommRingCat.ofHom (chartFibreRingMap I a b hI ha hb).toRingHom))
      (quotientImmersion I)
      ((affineAtlas (blowupDatum (affineCenter A I))).chart
        (firstGenerator I a b hI) ≫ blowdown I) := by
    rw [fibreChart_snd, (affineAtlas (blowupDatum (affineCenter A I))).triangle]
    exact (chartFibreSquare I a b hI ha hb).flip
  exact H.of_right (fibreChart_fst I a b hI ha hb)
    (IsPullback.of_hasPullback (blowdown I) (quotientImmersion I)).flip

instance fibreChartIsOpenImmersion : IsOpenImmersion (fibreChart I a b hI ha hb) := by
  let := (affineAtlas (blowupDatum (affineCenter A I))).openImmersion
    (firstGenerator I a b hI)
  exact MorphismProperty.of_isPullback (fibreChart_isPullback I a b hI ha hb).flip
    inferInstance

/-- Its image is exactly the inverse image of the original saturated-chart image. -/
theorem fibreChart_range : Set.range (fibreChart I a b hI ha hb) =
    exceptionalι I ⁻¹' Set.range
      ((affineAtlas (blowupDatum (affineCenter A I))).chart (firstGenerator I a b hI)) :=
  Scheme.Pullback.Fibre.pullback_range_fst (fibreChart_isPullback I a b hI ha hb)

/-- The two original parameter charts cover the literal exceptional fibre. -/
theorem fibreCharts_cover (hb' : IsSMulRegular A b)
    (ha' : IsSMulRegular (A ⧸ Ideal.span {b}) a) (x : exceptionalFibre I) :
    x ∈ Set.range (fibreChart I a b hI ha hb) ∨
      x ∈ Set.range (fibreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha') := by
  let H := affineAtlas (blowupDatum (affineCenter A I))
  let g : Bool → I := fun i => if i then firstGenerator I a b hI else
    firstGenerator I b a (Ideal.span_pair_comm.trans hI)
  have hg : Ideal.span (Set.range fun i => (g i : A)) = I := by
    have he : Set.range (fun i => (g i : A)) = {a, b} := by
      ext r
      constructor
      · rintro ⟨i, rfl⟩
        cases i <;> simp [g, firstGenerator]
      · intro hr
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
        rcases hr with h | h
        · subst r
          exact ⟨true, rfl⟩
        · subst r
          exact ⟨false, rfl⟩
    rw [he]
    exact hI
  obtain ⟨i, hi⟩ := H.generator_covers g hg (exceptionalι I x)
  cases i
  · right
    rw [fibreChart_range]
    exact hi
  · left
    rw [fibreChart_range]
    exact hi

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Localization.Away
variable {A : Type u} [CommRing A]
variable (I : Ideal A) (a b : A) (hI : Ideal.span {a, b} = I)
  (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)

/-- The original polynomial quotient identifies with the actual saturated chart ring. -/
def chartAlgebraEquiv : pairQuotient a b ≃ₐ[A] affineBlowupAlgebra A I a := by
  subst I
  exact pairChartEquiv a b ha hb

/-- The forward polynomial chart coordinate is the literal atlas ratio. -/
theorem chartAlgebraEquiv_coordinate :
    chartAlgebraEquiv I a b hI ha hb (pairCoordinate a b) =
      ratio A I (firstGenerator I a b hI)
        (firstGenerator I b a (Ideal.span_pair_comm.trans hI)) := by
  subst I
  apply Subtype.ext
  exact pairChartEquiv_coordinate a b ha hb

/-- On the actual fibre chart, the original ratio reduces to the polynomial coordinate. -/
theorem chartFibreRingMap_coordinate :
    chartFibreRingMap I a b hI ha hb
      (ratio A I (firstGenerator I a b hI)
        (firstGenerator I b a (Ideal.span_pair_comm.trans hI))) = X := by
  rw [← chartAlgebraEquiv_coordinate I a b hI ha hb]
  subst I
  exact pairChartFibreEquiv_coordinate a b ha hb

/-- The polynomial quotient chart in the same actual constructed blowup. -/
def rawChart : Spec (.of (pairQuotient a b)) ⟶ canonicalBlowup I :=
  Spec.map (CommRingCat.ofHom (chartAlgebraEquiv I a b hI ha hb).symm.toRingHom) ≫
    (affineAtlas (blowupDatum (affineCenter A I))).chart (firstGenerator I a b hI)

instance rawChartIsOpenImmersion : IsOpenImmersion (rawChart I a b hI ha hb) := by
  let := (affineAtlas (blowupDatum (affineCenter A I))).openImmersion
    (firstGenerator I a b hI)
  let e := Scheme.Spec.mapIso
    (chartAlgebraEquiv I a b hI ha hb).symm.toRingEquiv.toCommRingCatIso.op
  have : IsIso (Spec.map
      (CommRingCat.ofHom (chartAlgebraEquiv I a b hI ha hb).symm.toRingHom)) := e.isIso_hom
  unfold rawChart
  infer_instance

/-- The quotient chart retains the original structural map to the base spectrum. -/
theorem rawChart_base : rawChart I a b hI ha hb ≫ blowdown I =
    Spec.map (CommRingCat.ofHom (algebraMap A (pairQuotient a b))) := by
  rw [rawChart, Category.assoc,
    (affineAtlas (blowupDatum (affineCenter A I))).triangle]
  change Spec.map (CommRingCat.ofHom (chartAlgebraEquiv I a b hI ha hb).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (affineBlowupAlgebra A I a))) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (chartAlgebraEquiv I a b hI ha hb).symm.commutes r

/-- The original quotient-coordinate reduction to the actual polynomial fibre chart. -/
def rawChartReduction : pairQuotient a b →ₐ[A] (A ⧸ I)[X] :=
  (chartFibreRingMap I a b hI ha hb).comp (chartAlgebraEquiv I a b hI ha hb).toAlgHom

/-- Reduction retains the quotient coordinate. -/
theorem rawChartReduction_coordinate :
    rawChartReduction I a b hI ha hb (pairCoordinate a b) = X := by
  change chartFibreRingMap I a b hI ha hb
    (chartAlgebraEquiv I a b hI ha hb (pairCoordinate a b)) = X
  rw [chartAlgebraEquiv_coordinate, chartFibreRingMap_coordinate]

/-- The quotient-coordinate reduction gives exactly the earlier saturated fibre chart. -/
theorem rawChartReduction_chart :
    Spec.map (CommRingCat.ofHom (rawChartReduction I a b hI ha hb).toRingHom) ≫
      rawChart I a b hI ha hb = chartFibreToBlowup I a b hI ha hb := by
  unfold rawChart chartFibreToBlowup
  rw [← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change chartFibreRingMap I a b hI ha hb
    (chartAlgebraEquiv I a b hI ha hb ((chartAlgebraEquiv I a b hI ha hb).symm r)) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

variable (hb' : IsSMulRegular A b) (ha' : IsSMulRegular (A ⧸ Ideal.span {b}) a)

/-- The actual reciprocal chart maps agree in the constructed blowup. Universal uniqueness
is applied on the original Cartier chart overlap, before restriction to the fibre. -/
theorem rawChart_reciprocal :
    Spec.map (CommRingCat.ofHom
        (algebraMap (pairQuotient a b) (Localization.Away (pairCoordinate a b)))) ≫
      rawChart I a b hI ha hb =
    Spec.map (CommRingCat.ofHom (pairReciprocal a b).toRingHom) ≫
      rawChart I b a (Ideal.span_pair_comm.trans hI) hb' ha' := by
  let g := Spec.map (CommRingCat.ofHom
      (algebraMap (pairQuotient a b) (Localization.Away (pairCoordinate a b)))) ≫
    rawChart I a b hI ha hb
  have : IsOpenImmersion g := by dsimp [g]; infer_instance
  have hcart := cartierPullback_comp_of_isOpenImmersion (affineCenter A I)
    (blowdown I) (blowupDatum (affineCenter A I)).cartier g
  apply (blowupDatum (affineCenter A I)).hom_ext hcart rfl
  dsimp only [g]
  rw [Category.assoc, rawChart_base, Category.assoc, rawChart_base,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (pairReciprocal a b).commutes r

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Localization.Away
open Scheme.PolynomialLaurent

variable {A : Type u} [CommRing A]
variable (I : Ideal A) (a b : A) (hI : Ideal.span {a, b} = I)
  (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)

/-- The original quotient coordinate maps to the positive Laurent coordinate. -/
def rawLaurentMap : pairQuotient a b →ₐ[A] LaurentPolynomial (A ⧸ I) :=
  ((Polynomial.toLaurentAlg (R := A ⧸ I)).restrictScalars A).comp
    (rawChartReduction I a b hI ha hb)

theorem rawLaurentMap_coordinate :
    rawLaurentMap I a b hI ha hb (pairCoordinate a b) = LaurentPolynomial.T 1 := by
  change Polynomial.toLaurent (rawChartReduction I a b hI ha hb (pairCoordinate a b)) = _
  rw [rawChartReduction_coordinate, Polynomial.toLaurent_X]

theorem rawLaurentMap_isUnit_coordinate :
    IsUnit (rawLaurentMap I a b hI ha hb (pairCoordinate a b)) := by
  rw [rawLaurentMap_coordinate]
  exact (laurentCoordinateUnit (.of (A ⧸ I))).isUnit

/-- The actual localization map induced by the invertible Laurent coordinate. -/
def rawLaurentLift : Localization.Away (pairCoordinate a b) →ₐ[A]
    LaurentPolynomial (A ⧸ I) :=
  IsLocalization.Away.liftAlgHom (pairCoordinate a b)
    (f := rawLaurentMap I a b hI ha hb) (rawLaurentMap_isUnit_coordinate I a b hI ha hb)

theorem rawLaurentLift_base (q : pairQuotient a b) :
    rawLaurentLift I a b hI ha hb
      (algebraMap (pairQuotient a b) (Localization.Away (pairCoordinate a b)) q) =
    rawLaurentMap I a b hI ha hb q :=
  IsLocalization.Away.lift_eq (S := Localization.Away (pairCoordinate a b))
    (g := (rawLaurentMap I a b hI ha hb).toRingHom) (pairCoordinate a b)
    (rawLaurentMap_isUnit_coordinate I a b hI ha hb) q

theorem rawLaurentLift_invCoordinate :
    rawLaurentLift I a b hI ha hb (IsLocalization.Away.invSelf (pairCoordinate a b)) =
      LaurentPolynomial.T (-1) := by
  apply Localization.Away.map_invSelf_of_mul (pairCoordinate a b)
    (rawLaurentLift I a b hI ha hb).toRingHom (LaurentPolynomial.T (-1))
  change rawLaurentLift I a b hI ha hb
      (algebraMap (pairQuotient a b) (Localization.Away (pairCoordinate a b))
        (pairCoordinate a b)) * LaurentPolynomial.T (-1) = 1
  rw [rawLaurentLift_base I a b hI ha hb, rawLaurentMap_coordinate I a b hI ha hb,
    ← LaurentPolynomial.T_add]
  norm_num

variable (hb' : IsSMulRegular A b) (ha' : IsSMulRegular (A ⧸ Ideal.span {b}) a)

theorem rawLaurentLift_reciprocal :
    (rawLaurentLift I a b hI ha hb).comp (pairReciprocal a b) =
      ((LaurentPolynomial.invert (R := A ⧸ I)).restrictScalars A).toAlgHom.comp
        (rawLaurentMap I b a (Ideal.span_pair_comm.trans hI) hb' ha') := by
  apply AdjoinRoot.algHom_ext
  change rawLaurentLift I a b hI ha hb (pairReciprocal a b (pairCoordinate b a)) =
    LaurentPolynomial.invert
      (rawLaurentMap I b a (Ideal.span_pair_comm.trans hI) hb' ha' (pairCoordinate b a))
  rw [pairReciprocal_coordinate, rawLaurentLift_invCoordinate,
    rawLaurentMap_coordinate, LaurentPolynomial.invert_T]

theorem laurentPlus_rawChart :
    laurentPlus (.of (A ⧸ I)) ≫ chartFibreToBlowup I a b hI ha hb =
      Spec.map (CommRingCat.ofHom (rawLaurentMap I a b hI ha hb).toRingHom) ≫
        rawChart I a b hI ha hb := by
  rw [← rawChartReduction_chart, laurentPlus, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem laurentMinus_rawChart :
    laurentMinus (.of (A ⧸ I)) ≫
        chartFibreToBlowup I b a (Ideal.span_pair_comm.trans hI) hb' ha' =
      Spec.map (CommRingCat.ofHom
        (((LaurentPolynomial.invert (R := A ⧸ I)).restrictScalars A).toAlgHom.comp
          (rawLaurentMap I b a (Ideal.span_pair_comm.trans hI) hb' ha')).toRingHom) ≫
        rawChart I b a (Ideal.span_pair_comm.trans hI) hb' ha' := by
  rw [← rawChartReduction_chart, laurentMinus, ← Category.assoc, ← Spec.map_comp]
  rfl

/-- The actual fibre charts agree along the original positive and inverse Laurent maps. -/
theorem fibreCharts_laurent_compatibility :
    laurentPlus (.of (A ⧸ I)) ≫ fibreChart I a b hI ha hb =
      laurentMinus (.of (A ⧸ I)) ≫
        fibreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha' := by
  apply pullback.hom_ext
  · simp only [Category.assoc, fibreChart_fst]
    rw [laurentPlus_rawChart I a b hI ha hb, laurentMinus_rawChart I a b hI hb' ha']
    have h := congrArg
      (fun g : Spec (.of (Localization.Away (pairCoordinate a b))) ⟶ canonicalBlowup I =>
        Spec.map (CommRingCat.ofHom (rawLaurentLift I a b hI ha hb).toRingHom) ≫ g)
      (rawChart_reciprocal I a b hI ha hb hb' ha')
    have hbase :
        Spec.map (CommRingCat.ofHom (rawLaurentLift I a b hI ha hb).toRingHom) ≫
            Spec.map (CommRingCat.ofHom
              (algebraMap (pairQuotient a b) (Localization.Away (pairCoordinate a b)))) =
          Spec.map (CommRingCat.ofHom (rawLaurentMap I a b hI ha hb).toRingHom) := by
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      exact rawLaurentLift_base I a b hI ha hb
    have hinverse :
        Spec.map (CommRingCat.ofHom (rawLaurentLift I a b hI ha hb).toRingHom) ≫
            Spec.map (CommRingCat.ofHom (pairReciprocal a b).toRingHom) =
          Spec.map (CommRingCat.ofHom
            (((LaurentPolynomial.invert (R := A ⧸ I)).restrictScalars A).toAlgHom.comp
              (rawLaurentMap I b a (Ideal.span_pair_comm.trans hI) hb' ha')).toRingHom) := by
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      exact congrArg AlgHom.toRingHom (rawLaurentLift_reciprocal I a b hI ha hb hb' ha')
    simpa only [← Category.assoc, hbase, hinverse] using h
  · simp only [Category.assoc, fibreChart_snd, laurentPlus_projection, laurentMinus_projection]

end AlgebraicGeometry.Scheme.Blowup.RegularPoint

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Localization.Away
open Scheme.PolynomialLaurent

variable {A : Type u} [CommRing A]
variable (I : Ideal A) (a b : A) (hI : Ideal.span {a, b} = I)
  (ha : IsSMulRegular A a) (hb : IsSMulRegular (A ⧸ Ideal.span {a}) b)
  (hb' : IsSMulRegular A b) (ha' : IsSMulRegular (A ⧸ Ideal.span {b}) a)

/-- The actual intersection of the two polynomial fibre charts is the standard Laurent open. -/
theorem fibreChart_preimage_other :
    fibreChart I a b hI ha hb ⁻¹ᵁ
        (fibreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha').opensRange =
      (laurentPlus (.of (A ⧸ I))).opensRange := by
  let H := affineAtlas (blowupDatum (affineCenter A I))
  let ga := firstGenerator I a b hI
  let gb := firstGenerator I b a (Ideal.span_pair_comm.trans hI)
  let φ := chartFibreRingMap I a b hI ha hb
  let : IsOpenImmersion (H.chart ga) := H.openImmersion ga
  have hs : H.chart ga ⁻¹' Set.range (H.chart gb) =
      Set.range (affineOverlapMap A I ga gb) :=
    Scheme.Pullback.Fibre.preimage_range_of_overlap (affineOverlapMap A I ga gb)
      (H.chart ga) (H.chart gb) (H.overlap ga gb)
  rw [laurentPlus_opensRange]
  ext x
  change fibreChart I a b hI ha hb x ∈
      Set.range (fibreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha') ↔
    (X : (A ⧸ I)[X]) ∉ x.asIdeal
  rw [fibreChart_range]
  have ht : exceptionalι I (fibreChart I a b hI ha hb x) =
      H.chart ga ((Spec.map (CommRingCat.ofHom φ.toRingHom)) x) :=
    congrArg (fun f => f x) (fibreChart_fst I a b hI ha hb)
  change exceptionalι I (fibreChart I a b hI ha hb x) ∈ Set.range (H.chart gb) ↔ _
  rw [ht]
  change (Spec.map (CommRingCat.ofHom φ.toRingHom)) x ∈
    H.chart ga ⁻¹' Set.range (H.chart gb) ↔ _
  rw [hs]
  change PrimeSpectrum.comap φ.toRingHom x ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (affineBlowupAlgebra A I ga) (Localization.Away (ratio A I ga gb)))) ↔ _
  rw [PrimeSpectrum.localization_away_comap_range
    (Localization.Away (ratio A I ga gb)) (ratio A I ga gb)]
  change φ (ratio A I ga gb) ∉ x.asIdeal ↔ (X : (A ⧸ I)[X]) ∉ x.asIdeal
  rw [chartFibreRingMap_coordinate]

/-- The two original polynomial fibre charts glue by the proved reciprocal equation. -/
def twoChartToExceptional :
    Scheme.ProjectiveLine.TwoChart.twoChartLine (.of (A ⧸ I)) ⟶ exceptionalFibre I :=
  pushout.desc (fibreChart I a b hI ha hb)
    (fibreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha')
    (fibreCharts_laurent_compatibility I a b hI ha hb hb' ha')

instance twoChartToExceptionalIsIso : IsIso (twoChartToExceptional I a b hI ha hb hb' ha') := by
  apply Scheme.OpenPushoutIso.desc_isIso (laurentPlus (.of (A ⧸ I)))
    (laurentMinus (.of (A ⧸ I))) (fibreChart I a b hI ha hb)
    (fibreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha')
    (fibreCharts_laurent_compatibility I a b hI ha hb hb' ha')
    (fibreChart_preimage_other I a b hI ha hb hb' ha')
  exact fibreCharts_cover I a b hI ha hb hb' ha'

/-- The actual polynomial pushout is the same exceptional fibre, through its original charts. -/
def twoChartExceptionalIso :
    Scheme.ProjectiveLine.TwoChart.twoChartLine (.of (A ⧸ I)) ≅ exceptionalFibre I :=
  asIso (twoChartToExceptional I a b hI ha hb hb' ha')

@[reassoc (attr := simp)]
theorem twoChartExceptionalIso_plus :
    Scheme.ProjectiveLine.TwoChart.plusChart (.of (A ⧸ I)) ≫
      (twoChartExceptionalIso I a b hI ha hb hb' ha').hom = fibreChart I a b hI ha hb :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem twoChartExceptionalIso_minus :
    Scheme.ProjectiveLine.TwoChart.minusChart (.of (A ⧸ I)) ≫
      (twoChartExceptionalIso I a b hI ha hb hb' ha').hom =
    fibreChart I b a (Ideal.span_pair_comm.trans hI) hb' ha' :=
  pushout.inr_desc _ _ _

theorem twoChartExceptionalIso_over :
    (twoChartExceptionalIso I a b hI ha hb hb' ha').hom ≫ exceptionalStructureMap I =
      Scheme.ProjectiveLine.TwoChart.projection (.of (A ⧸ I)) := by
  apply pushout.hom_ext
  · change ProjectiveLine.TwoChart.plusChart (.of (A ⧸ I)) ≫
        ((twoChartExceptionalIso I a b hI ha hb hb' ha').hom ≫ exceptionalStructureMap I) =
      ProjectiveLine.TwoChart.plusChart (.of (A ⧸ I)) ≫
        ProjectiveLine.TwoChart.projection (.of (A ⧸ I))
    rw [← Category.assoc, twoChartExceptionalIso_plus I a b hI ha hb hb' ha',
      fibreChart_snd I a b hI ha hb]
    exact (Scheme.ProjectiveLine.TwoChart.plusChart_projection (.of (A ⧸ I))).symm
  · change ProjectiveLine.TwoChart.minusChart (.of (A ⧸ I)) ≫
        ((twoChartExceptionalIso I a b hI ha hb hb' ha').hom ≫ exceptionalStructureMap I) =
      ProjectiveLine.TwoChart.minusChart (.of (A ⧸ I)) ≫
        ProjectiveLine.TwoChart.projection (.of (A ⧸ I))
    rw [← Category.assoc, twoChartExceptionalIso_minus I a b hI ha hb hb' ha',
      fibreChart_snd I b a (Ideal.span_pair_comm.trans hI) hb' ha']
    exact (Scheme.ProjectiveLine.TwoChart.minusChart_projection (.of (A ⧸ I))).symm

/-- The two-chart identification preserves the original quotient structural map. -/
def twoChartExceptionalOverIso :
    Over.mk (Scheme.ProjectiveLine.TwoChart.projection (.of (A ⧸ I))) ≅
      Over.mk (exceptionalStructureMap I) :=
  Over.isoMk (twoChartExceptionalIso I a b hI ha hb hb' ha')
    (twoChartExceptionalIso_over I a b hI ha hb hb' ha')

end AlgebraicGeometry.Scheme.Blowup.RegularPoint
