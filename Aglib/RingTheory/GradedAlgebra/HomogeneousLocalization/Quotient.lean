/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.GradedAlgebra.HomogeneousLocalization.DegreeOne
public import Aglib.RingTheory.GradedAlgebra.Quotient


/-!
# Homogeneous degree-one charts of actual quotients

The quotient of the actual degree-zero chart by the image of a homogeneous
ideal is the actual degree-zero chart of the homogeneous quotient. The proof
uses degree-one dehomogenization and commutation of the two quotient ideals.

The comparison retains every original numerator, denominator and coefficient.
It requires no flatness, domain or Noetherian hypothesis. Its current consumer
is the exceptional chart of the actual Rees quotient defining the associated
graded ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

namespace HomogeneousLocalization.Away

variable {R D : Type u} [CommRing R] [CommRing D] [Algebra R D]
  (G : ℕ → Submodule R D) [GradedAlgebra G] (J : Ideal D) {f : D}

omit [GradedAlgebra G] in
/-- The actual quotient denominator retains its original degree one. -/
theorem quotientDenominator_mem (hf : f ∈ G 1) :
    Ideal.Quotient.mk J f ∈ GradedAlgebra.Quotient.grading G J 1 :=
  Submodule.mem_map.mpr ⟨f, hf, rfl⟩

/-- The original homogeneous ideal has its actual quotient image after dehomogenization. -/
theorem dehomogenizedIdeal_map (hf : f ∈ G 1) :
    (J.map (dehomogenize G hf)).map (degreeOneQuotientEquiv G hf).toRingHom =
      J.map (Ideal.Quotient.mk (dehomogenizingIdeal (f := f))) := by
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro x
  exact toQuotient_dehomogenize G hf x

/-- Quotienting keeps the same original relation setting f equal to one. -/
theorem dehomogenizingIdeal_quotient_map :
    (dehomogenizingIdeal (f := f)).map (Ideal.Quotient.mk J) =
      dehomogenizingIdeal (f := Ideal.Quotient.mk J f) := by
  simp only [dehomogenizingIdeal, Ideal.map_span, Set.image_singleton, map_sub, map_one]

/-- The actual quotient of the original degree-zero chart is the actual chart
of the homogeneous quotient, through the original numerator and denominator maps. -/
def homogeneousQuotientEquiv (hJ : J.IsHomogeneous G) (hf : f ∈ G 1) :
    let _ := GradedAlgebra.Quotient.gradedAlgebra G J hJ
    (Away G f) ⧸ J.map (dehomogenize G hf) ≃+*
      Away (GradedAlgebra.Quotient.grading G J) (Ideal.Quotient.mk J f) := by
  let := GradedAlgebra.Quotient.gradedAlgebra G J hJ
  exact (Ideal.quotientEquiv _ _ (degreeOneQuotientEquiv G hf)
      (dehomogenizedIdeal_map G J hf).symm).trans
    ((DoubleQuot.quotQuotEquivComm (dehomogenizingIdeal (f := f)) J).trans
      ((Ideal.quotEquivOfEq (dehomogenizingIdeal_quotient_map J (f := f))).trans
        (degreeOneQuotientEquiv (GradedAlgebra.Quotient.grading G J)
          (quotientDenominator_mem G J hf)).symm))

/-- Every original element is preserved after its actual dehomogenization and quotient. -/
theorem homogeneousQuotientEquiv_mk_dehomogenize
    (hJ : J.IsHomogeneous G) (hf : f ∈ G 1) (x : D) :
    let _ := GradedAlgebra.Quotient.gradedAlgebra G J hJ
    homogeneousQuotientEquiv G J hJ hf
      (Ideal.Quotient.mk (J.map (dehomogenize G hf)) (dehomogenize G hf x)) =
      dehomogenize (GradedAlgebra.Quotient.grading G J)
        (quotientDenominator_mem G J hf) (Ideal.Quotient.mk J x) := by
  let := GradedAlgebra.Quotient.gradedAlgebra G J hJ
  let e0 := Ideal.quotientEquiv _ _ (degreeOneQuotientEquiv G hf)
    (dehomogenizedIdeal_map G J hf).symm
  let e1 := DoubleQuot.quotQuotEquivComm (dehomogenizingIdeal (f := f)) J
  let e2 := Ideal.quotEquivOfEq (dehomogenizingIdeal_quotient_map J (f := f))
  let e3 := degreeOneQuotientEquiv (GradedAlgebra.Quotient.grading G J)
    (quotientDenominator_mem G J hf)
  have he : degreeOneQuotientEquiv G hf (dehomogenize G hf x) =
      Ideal.Quotient.mk (dehomogenizingIdeal (f := f)) x :=
    toQuotient_dehomogenize G hf x
  have h0 : e0 (Ideal.Quotient.mk (J.map (dehomogenize G hf)) (dehomogenize G hf x)) =
      DoubleQuot.quotQuotMk (dehomogenizingIdeal (f := f)) J x :=
    (Ideal.quotientEquiv_mk _ _ (degreeOneQuotientEquiv G hf)
      (dehomogenizedIdeal_map G J hf).symm (dehomogenize G hf x)).trans
        (congrArg (Ideal.Quotient.mk
          (J.map (Ideal.Quotient.mk (dehomogenizingIdeal (f := f))))) he)
  change e3.symm (e2 (e1 (e0
    (Ideal.Quotient.mk (J.map (dehomogenize G hf)) (dehomogenize G hf x))))) = _
  calc
    _ = e3.symm (e2 (e1 (DoubleQuot.quotQuotMk (dehomogenizingIdeal (f := f)) J x))) :=
      congrArg (fun y => e3.symm (e2 (e1 y))) h0
    _ = e3.symm (e2 (DoubleQuot.quotQuotMk J (dehomogenizingIdeal (f := f)) x)) :=
      congrArg (fun y => e3.symm (e2 y))
        (DoubleQuot.quotQuotEquivComm_quotQuotMk (dehomogenizingIdeal (f := f)) J x)
    _ = e3.symm (Ideal.Quotient.mk
        (dehomogenizingIdeal (f := Ideal.Quotient.mk J f)) (Ideal.Quotient.mk J x)) :=
      congrArg e3.symm (Ideal.quotEquivOfEq_mk
        (dehomogenizingIdeal_quotient_map J (f := f)) (Ideal.Quotient.mk J x))
    _ = _ := fromQuotient_mk (GradedAlgebra.Quotient.grading G J)
      (quotientDenominator_mem G J hf) (Ideal.Quotient.mk J x)

/-- The quotient comparison maps each original homogeneous fraction to the same
fraction of its actual quotient numerator, with the original denominator retained. -/
theorem homogeneousQuotientEquiv_mk_fraction
    (hJ : J.IsHomogeneous G) (hf : f ∈ G 1) (n : ℕ) (x : D) (hx : x ∈ G n) :
    let _ := GradedAlgebra.Quotient.gradedAlgebra G J hJ
    homogeneousQuotientEquiv G J hJ hf
      (Ideal.Quotient.mk (J.map (dehomogenize G hf))
        (Away.mk G hf n x (by simpa only [smul_eq_mul, mul_one] using hx))) =
      Away.mk (GradedAlgebra.Quotient.grading G J) (quotientDenominator_mem G J hf) n
        (Ideal.Quotient.mk J x)
        (by simpa only [smul_eq_mul, mul_one] using
          (show Ideal.Quotient.mk J x ∈ GradedAlgebra.Quotient.grading G J n from
            Submodule.mem_map.mpr ⟨x, hx, rfl⟩)) := by
  let := GradedAlgebra.Quotient.gradedAlgebra G J hJ
  have h : homogeneousQuotientEquiv G J hJ hf
      (Ideal.Quotient.mk (J.map (dehomogenize G hf)) (dehomogenize G hf x)) =
      dehomogenize (GradedAlgebra.Quotient.grading G J)
        (quotientDenominator_mem G J hf) (Ideal.Quotient.mk J x) :=
    homogeneousQuotientEquiv_mk_dehomogenize G J hJ hf x
  rw [dehomogenize_homogeneous G hf x hx,
    dehomogenize_homogeneous (GradedAlgebra.Quotient.grading G J)
      (quotientDenominator_mem G J hf) (Ideal.Quotient.mk J x)
      (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)] at h
  exact h

end HomogeneousLocalization.Away
