/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.GradedAlgebra.HomogeneousLocalization.Quotient
public import Aglib.RingTheory.ReesAlgebra.Away
public import Aglib.RingTheory.AssociatedGraded.Basic
public import Aglib.RingTheory.Blowup.WeakTransform
public import Aglib.RingTheory.Localization.Away.SaturatedChartLift


/-!
# The actual exceptional quotient of a saturated blowup chart

The original saturated chart modulo its exceptional parameter is the
homogeneous chart of the actual associated graded ring. The proof combines
Rees dehomogenization, the exact image of the centre ideal, and homogeneous
quotient compatibility. It retains the original coefficient map and every
original fraction b/a, with the same degree-one denominator aX.

The associated graded ring is the quotient of the original Rees algebra by
the extended centre ideal. No flatness, domain, Noetherian or tangent-equation
hypothesis is required. The actual tangent-square identification and the
normality of the geometric blowup remain inputs of later point arguments.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

namespace HomogeneousLocalization.Away

variable {R D S : Type u} [CommRing R] [CommRing D] [CommRing S] [Algebra R D]
  (G : ℕ → Submodule R D) [GradedAlgebra G] (J : Ideal D)
  (H : ℕ → Submodule R (D ⧸ J)) [GradedAlgebra H] {f : D}

/-- Construct the quotient chart in its given original target grading,
retaining the supplied original affine-chart equivalence. -/
def chartQuotientEquiv (hf : f ∈ G 1) (hfQ : Ideal.Quotient.mk J f ∈ H 1)
    (e : Away G f ≃+* S) (K : Ideal S)
    (hK : K = (J.map (dehomogenize G hf)).map e.toRingHom) :
    S ⧸ K ≃+* Away H (Ideal.Quotient.mk J f) :=
  (Ideal.quotientEquiv _ _ e hK).symm.trans
    ((Ideal.quotientEquiv _ _ (degreeOneQuotientEquiv G hf)
      (dehomogenizedIdeal_map G J hf).symm).trans
      ((DoubleQuot.quotQuotEquivComm (dehomogenizingIdeal (f := f)) J).trans
        ((Ideal.quotEquivOfEq (dehomogenizingIdeal_quotient_map J (f := f))).trans
          (degreeOneQuotientEquiv H hfQ).symm)))

private theorem chartQuotientEquiv_mk_dehomogenize
    (hf : f ∈ G 1) (hfQ : Ideal.Quotient.mk J f ∈ H 1)
    (e : Away G f ≃+* S) (K : Ideal S)
    (hK : K = (J.map (dehomogenize G hf)).map e.toRingHom) (x : D) :
    chartQuotientEquiv G J H hf hfQ e K hK
      (Ideal.Quotient.mk K (e.toRingHom (dehomogenize G hf x))) =
      dehomogenize H hfQ (Ideal.Quotient.mk J x) := by
  let eS := Ideal.quotientEquiv _ _ e hK
  let eG := Ideal.quotientEquiv _ _ (degreeOneQuotientEquiv G hf)
    (dehomogenizedIdeal_map G J hf).symm
  let eC := DoubleQuot.quotQuotEquivComm (dehomogenizingIdeal (f := f)) J
  let eQ := Ideal.quotEquivOfEq (dehomogenizingIdeal_quotient_map J (f := f))
  let eH := degreeOneQuotientEquiv H hfQ
  have hS : eS.symm (Ideal.Quotient.mk K (e.toRingHom (dehomogenize G hf x))) =
      Ideal.Quotient.mk (J.map (dehomogenize G hf)) (dehomogenize G hf x) :=
    (Ideal.quotientEquiv_symm_mk _ _ e hK (e.toRingHom (dehomogenize G hf x))).trans
      (congrArg (Ideal.Quotient.mk (J.map (dehomogenize G hf)))
        (e.symm_apply_apply (dehomogenize G hf x)))
  have hG : eG (Ideal.Quotient.mk (J.map (dehomogenize G hf)) (dehomogenize G hf x)) =
      DoubleQuot.quotQuotMk (dehomogenizingIdeal (f := f)) J x :=
    (Ideal.quotientEquiv_mk _ _ (degreeOneQuotientEquiv G hf)
      (dehomogenizedIdeal_map G J hf).symm (dehomogenize G hf x)).trans
        (congrArg (Ideal.Quotient.mk
          (J.map (Ideal.Quotient.mk (dehomogenizingIdeal (f := f)))))
            (toQuotient_dehomogenize G hf x))
  change eH.symm (eQ (eC (eG (eS.symm
    (Ideal.Quotient.mk K (e.toRingHom (dehomogenize G hf x))))))) = _
  calc
    _ = eH.symm (eQ (eC (eG
        (Ideal.Quotient.mk (J.map (dehomogenize G hf)) (dehomogenize G hf x))))) :=
      congrArg (fun y => eH.symm (eQ (eC (eG y)))) hS
    _ = eH.symm (eQ (eC (DoubleQuot.quotQuotMk (dehomogenizingIdeal (f := f)) J x))) :=
      congrArg (fun y => eH.symm (eQ (eC y))) hG
    _ = eH.symm (eQ (DoubleQuot.quotQuotMk J (dehomogenizingIdeal (f := f)) x)) :=
      congrArg (fun y => eH.symm (eQ y))
        (DoubleQuot.quotQuotEquivComm_quotQuotMk (dehomogenizingIdeal (f := f)) J x)
    _ = eH.symm (Ideal.Quotient.mk
        (dehomogenizingIdeal (f := Ideal.Quotient.mk J f)) (Ideal.Quotient.mk J x)) :=
      congrArg eH.symm (Ideal.quotEquivOfEq_mk
        (dehomogenizingIdeal_quotient_map J (f := f)) (Ideal.Quotient.mk J x))
    _ = _ := fromQuotient_mk H hfQ (Ideal.Quotient.mk J x)

end HomogeneousLocalization.Away

namespace reesAlgebra

open HomogeneousLocalization

variable {A : Type u} [CommRing A] (I : Ideal A) (a : I)

/-- The actual Rees dehomogenization into its original saturated chart. -/
def chartDehomogenize : reesAlgebra I →+*
    Localization.Away.saturatedChart A I (a : A) :=
  (awayEquiv I a).toRingHom.comp
    (Away.dehomogenize (grading I) (degreeOne_mem I a))

/-- Dehomogenization retains the original coefficient ring map. -/
theorem chartDehomogenize_comp :
    (chartDehomogenize I a).comp (algebraMap A (reesAlgebra I)) =
      algebraMap A (Localization.Away.saturatedChart A I (a : A)) := by
  apply RingHom.ext
  intro r
  change awayEquiv I a
    (Away.dehomogenize (grading I) (degreeOne_mem I a)
      (algebraMap A (reesAlgebra I) r)) = _
  rw [← degreeZeroEquiv_symm_coe, Away.dehomogenize_fromZero]
  exact awayEquiv_base I a r

/-- The homogeneous ideal defining the associated graded becomes the literal
exceptional principal ideal in the original saturated chart. -/
theorem chartDehomogenize_associatedGradedIdeal :
    I.associatedGradedIdeal.map (chartDehomogenize I a) =
      Ideal.span {algebraMap A (Localization.Away.saturatedChart A I (a : A)) (a : A)} := by
  rw [Ideal.associatedGradedIdeal, Ideal.map_map, chartDehomogenize_comp]
  exact Localization.Away.map_center_eq_span I (a : A) a.property

/-- The same ideal equality in the original homogeneous-chart coordinates. -/
theorem awayEquiv_dehomogenizedAssociatedIdeal :
    (I.associatedGradedIdeal.map
      (Away.dehomogenize (grading I) (degreeOne_mem I a))).map
        (awayEquiv I a).toRingHom =
      Ideal.span {algebraMap A (Localization.Away.saturatedChart A I (a : A)) (a : A)} := by
  rw [Ideal.map_map]
  exact chartDehomogenize_associatedGradedIdeal I a

/-- The original degree-one element in the original associated graded component. -/
theorem degreeOne_associatedGraded_mem :
    Ideal.Quotient.mk I.associatedGradedIdeal (degreeOne I a) ∈
      I.associatedGradedGrading 1 := by
  change Ideal.Quotient.mk I.associatedGradedIdeal (degreeOne I a) ∈
    (grading I 1).map (Ideal.Quotient.mkₐ A I.associatedGradedIdeal).toLinearMap
  exact Submodule.mem_map.mpr ⟨degreeOne I a, degreeOne_mem I a, rfl⟩

/-- The actual exceptional chart quotient equals the degree-zero chart of the
actual associated graded ring, with the same original degree-one denominator. -/
def exceptionalChartEquiv :
    (Localization.Away.saturatedChart A I (a : A)) ⧸
        Ideal.span {algebraMap A (Localization.Away.saturatedChart A I (a : A)) (a : A)} ≃+*
      HomogeneousLocalization.Away I.associatedGradedGrading
        (Ideal.Quotient.mk I.associatedGradedIdeal (degreeOne I a)) :=
  Away.chartQuotientEquiv (R := A) (D := reesAlgebra I)
    (S := Localization.Away.saturatedChart A I (a : A))
    (grading I) I.associatedGradedIdeal I.associatedGradedGrading
    (degreeOne_mem I a) (degreeOne_associatedGraded_mem I a) (awayEquiv I a).toRingEquiv
    (Ideal.span {algebraMap A (Localization.Away.saturatedChart A I (a : A)) (a : A)})
    (awayEquiv_dehomogenizedAssociatedIdeal I a).symm

/-- Every original Rees numerator is preserved by the exceptional comparison. -/
theorem exceptionalChartEquiv_mk_dehomogenize (x : reesAlgebra I) :
    exceptionalChartEquiv I a
      (Ideal.Quotient.mk
        (Ideal.span {algebraMap A (Localization.Away.saturatedChart A I (a : A)) (a : A)})
        (chartDehomogenize I a x)) =
      Away.dehomogenize I.associatedGradedGrading (degreeOne_associatedGraded_mem I a)
        (Ideal.Quotient.mk I.associatedGradedIdeal x) := by
  simpa only [exceptionalChartEquiv, chartDehomogenize, RingHom.comp_apply] using
    Away.chartQuotientEquiv_mk_dehomogenize (R := A) (D := reesAlgebra I)
      (S := Localization.Away.saturatedChart A I (a : A))
      (grading I) I.associatedGradedIdeal I.associatedGradedGrading
      (degreeOne_mem I a) (degreeOne_associatedGraded_mem I a) (awayEquiv I a).toRingEquiv
      (Ideal.span {algebraMap A (Localization.Away.saturatedChart A I (a : A)) (a : A)})
      (awayEquiv_dehomogenizedAssociatedIdeal I a).symm x

/-- The actual original coefficient map is retained after passing to the exceptional fibre. -/
theorem exceptionalChartEquiv_mk_base (r : A) :
    exceptionalChartEquiv I a
      (Ideal.Quotient.mk
        (Ideal.span {algebraMap A (Localization.Away.saturatedChart A I (a : A)) (a : A)})
        (algebraMap A (Localization.Away.saturatedChart A I (a : A)) r)) =
      Away.dehomogenize I.associatedGradedGrading (degreeOne_associatedGraded_mem I a)
        (Ideal.Quotient.mk I.associatedGradedIdeal (algebraMap A (reesAlgebra I) r)) := by
  have h := exceptionalChartEquiv_mk_dehomogenize I a (algebraMap A (reesAlgebra I) r)
  have hc := congrArg (fun f : A →+* Localization.Away.saturatedChart A I (a : A) => f r)
    (chartDehomogenize_comp I a)
  exact hc ▸ h

/-- A degree-one original Rees numerator gives exactly the original chart fraction. -/
theorem chartDehomogenize_degreeOne (b : I) :
    chartDehomogenize I a (degreeOne I b) =
      Localization.Away.SaturatedChart.fractionElement I a b := by
  change awayEquiv I a
    (Away.dehomogenize (grading I) (degreeOne_mem I a) (degreeOne I b)) = _
  rw [Away.dehomogenize_homogeneous (grading I) (degreeOne_mem I a)
    (degreeOne I b) (degreeOne_mem I b)]
  apply Subtype.ext
  exact awayEquiv_ratio I a b

/-- Each original b/a goes to the same homogeneous fraction in the actual
associated graded chart; neither its numerator nor denominator is replaced. -/
theorem exceptionalChartEquiv_mk_fraction (b : I) :
    exceptionalChartEquiv I a
      (Ideal.Quotient.mk
        (Ideal.span {algebraMap A (Localization.Away.saturatedChart A I (a : A)) (a : A)})
        (Localization.Away.SaturatedChart.fractionElement I a b)) =
      HomogeneousLocalization.Away.mk I.associatedGradedGrading
        (degreeOne_associatedGraded_mem I a)
        1 (Ideal.Quotient.mk I.associatedGradedIdeal (degreeOne I b))
        (by simpa only [one_smul] using degreeOne_associatedGraded_mem I b) := by
  have h := exceptionalChartEquiv_mk_dehomogenize I a (degreeOne I b)
  rw [chartDehomogenize_degreeOne,
    Away.dehomogenize_homogeneous I.associatedGradedGrading
      (degreeOne_associatedGraded_mem I a)
      (Ideal.Quotient.mk I.associatedGradedIdeal (degreeOne I b))
      (degreeOne_associatedGraded_mem I b)] at h
  exact h

end reesAlgebra
