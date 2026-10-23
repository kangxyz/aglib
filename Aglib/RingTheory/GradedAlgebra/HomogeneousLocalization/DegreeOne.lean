/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Degree-one homogeneous localization as an actual quotient

For an original nonnegatively graded commutative ring and an element `f`
of degree one, its degree-zero localization is the quotient setting `f`
equal to one. The maps use the actual direct-sum decomposition and the
ordinary localization lift. No domain, reducedness, flatness or finite
generation hypothesis is used; zero and nilpotent denominators are included.

The current consumer is the nonflat scalar-extension comparison for
degree-one Rees charts. Its tensor and scheme comparisons are separate.
-/

@[expose] public noncomputable section

open Graded DirectSum

universe u

namespace HomogeneousLocalization.Away

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (G : ℕ → σ) [GradedRing G] {f : A}

/-- A homogeneous numerator divided by the matching power of the original denominator. -/
def degreeOneFraction (hf : f ∈ G 1) (n : ℕ) : G n →+ Away G f where
  toFun a := Away.mk G hf n a (by simpa only [smul_eq_mul, mul_one] using a.property)
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    simp only [Away.val_mk, HomogeneousLocalization.val_zero,
      ZeroMemClass.coe_zero, Localization.mk_zero]
  map_add' a b := by
    apply HomogeneousLocalization.val_injective
    rw [Away.val_mk, HomogeneousLocalization.val_add, Away.val_mk, Away.val_mk]
    exact (Localization.add_mk_self _ _ _).symm

/-- The degree-zero unit gives the unit fraction. -/
theorem degreeOneFraction_one (hf : f ∈ G 1) :
    degreeOneFraction G hf 0
      (GradedMonoid.GOne.one (A := fun n : ℕ => ↥(G n))) = 1 := by
  apply HomogeneousLocalization.val_injective
  simp [degreeOneFraction]

/-- Multiplication adds the original numerator and denominator degrees. -/
theorem degreeOneFraction_mul (hf : f ∈ G 1) {i j : ℕ} (a : G i) (b : G j) :
    degreeOneFraction G hf (i + j)
        (GradedMonoid.GMul.mul (A := fun n : ℕ => ↥(G n)) a b) =
      degreeOneFraction G hf i a * degreeOneFraction G hf j b := by
  apply HomogeneousLocalization.val_injective
  simp [degreeOneFraction, Localization.mk_mul, pow_add]

/-- Dehomogenize every homogeneous summand by the matching power of the
original degree-one denominator. -/
def dehomogenize (hf : f ∈ G 1) : A →+* Away G f :=
  (DirectSum.toSemiring (degreeOneFraction G hf) (degreeOneFraction_one G hf)
    (degreeOneFraction_mul G hf)).comp (DirectSum.decomposeRingEquiv G).toRingHom

/-- Dehomogenization on an original homogeneous numerator is the original fraction. -/
theorem dehomogenize_homogeneous (hf : f ∈ G 1) {n : ℕ} (a : A) (ha : a ∈ G n) :
    dehomogenize G hf a = Away.mk G hf n a
      (by simpa only [smul_eq_mul, mul_one] using ha) := by
  change DirectSum.toSemiring (degreeOneFraction G hf) (degreeOneFraction_one G hf)
    (degreeOneFraction_mul G hf) (DirectSum.decompose G a) = _
  rw [DirectSum.decompose_of_mem G ha, DirectSum.toSemiring_of]
  rfl

/-- The degree-one denominator dehomogenizes to one, including nilpotent cases. -/
theorem dehomogenize_denominator (hf : f ∈ G 1) : dehomogenize G hf f = 1 := by
  rw [dehomogenize_homogeneous G hf f hf]
  apply HomogeneousLocalization.val_injective
  simpa only [Away.val_mk, pow_one, HomogeneousLocalization.val_one] using
    (Localization.mk_self (⟨f, ⟨1, by simp⟩⟩ : Submonoid.powers f))

/-- The original ideal imposing the equation `f = 1`. -/
def dehomogenizingIdeal : Ideal A := Ideal.span ({f - 1} : Set A)

/-- The specified denominator is exactly one in the actual quotient ring. -/
theorem quotient_denominator :
    Ideal.Quotient.mk (dehomogenizingIdeal (f := f)) f = 1 :=
  (Ideal.Quotient.mk_eq_one_iff_sub_mem f).mpr
    (Ideal.subset_span (Set.mem_singleton _))

/-- The original denominator is a unit in the quotient setting it equal to one. -/
theorem quotient_denominator_isUnit :
    IsUnit (Ideal.Quotient.mk (dehomogenizingIdeal (f := f)) f) := by
  rw [quotient_denominator]
  exact isUnit_one

/-- The actual dehomogenization map descended through its proved relation. -/
def fromQuotient (hf : f ∈ G 1) : (A ⧸ dehomogenizingIdeal (f := f)) →+* Away G f :=
  Ideal.Quotient.lift (dehomogenizingIdeal (f := f)) (dehomogenize G hf) (by
    have hker : dehomogenizingIdeal (f := f) ≤ RingHom.ker (dehomogenize G hf) := by
      rw [dehomogenizingIdeal, Ideal.span_le]
      intro a ha
      obtain rfl := Set.mem_singleton_iff.mp ha
      change dehomogenize G hf (f - 1) = 0
      rw [map_sub, dehomogenize_denominator, map_one, sub_self]
    exact fun a ha => hker ha)

/-- Quotient descent retains the original dehomogenization map. -/
theorem fromQuotient_mk (hf : f ∈ G 1) (a : A) :
    fromQuotient G hf (Ideal.Quotient.mk (dehomogenizingIdeal (f := f)) a) =
      dehomogenize G hf a := rfl

/-- Restrict the ordinary localization lift of the original quotient map. -/
def toQuotient : Away G f →+* (A ⧸ dehomogenizingIdeal (f := f)) :=
  (IsLocalization.Away.lift f (quotient_denominator_isUnit (f := f))).comp
        (algebraMap (Away G f) (Localization.Away f))

/-- A homogeneous fraction maps to the original numerator class. -/
theorem toQuotient_mk (hf : f ∈ G 1) (n : ℕ) (a : A) (ha : a ∈ G (n • 1)) :
    toQuotient G (Away.mk G hf n a ha) =
      Ideal.Quotient.mk (dehomogenizingIdeal (f := f)) a := by
  change IsLocalization.Away.lift f (quotient_denominator_isUnit (f := f))
    (Away.mk G hf n a ha).val = _
  rw [Away.val_mk, Localization.mk_eq_mk']
  unfold IsLocalization.Away.lift
  rw [IsLocalization.lift_mk'_spec]
  change Ideal.Quotient.mk (dehomogenizingIdeal (f := f)) a =
    Ideal.Quotient.mk (dehomogenizingIdeal (f := f)) (f ^ n) *
      Ideal.Quotient.mk (dehomogenizingIdeal (f := f)) a
  rw [map_pow, quotient_denominator, one_pow, one_mul]

/-- The original homogeneous fraction is recovered from its quotient class. -/
theorem fromQuotient_toQuotient (hf : f ∈ G 1) (a : Away G f) :
    fromQuotient G hf (toQuotient G a) = a := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective G hf a
  rw [toQuotient_mk, fromQuotient_mk]
  have ha' : a ∈ G n := by simpa only [smul_eq_mul, mul_one] using ha
  exact dehomogenize_homogeneous G hf a ha'

/-- The composite on the original graded ring is its original quotient map. -/
theorem toQuotient_dehomogenize (hf : f ∈ G 1) (a : A) :
    toQuotient G (dehomogenize G hf a) =
      Ideal.Quotient.mk (dehomogenizingIdeal (f := f)) a := by
  induction a using DirectSum.Decomposition.inductionOn G with
  | zero => simp only [map_zero]
  | @homogeneous n a =>
    rw [dehomogenize_homogeneous G hf (a : A) a.property, toQuotient_mk]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The original quotient element is recovered after dehomogenization. -/
theorem toQuotient_fromQuotient (hf : f ∈ G 1) (a : A ⧸ dehomogenizingIdeal (f := f)) :
    toQuotient G (fromQuotient G hf a) = a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [fromQuotient_mk, toQuotient_dehomogenize]

/-- The actual degree-zero localization in a degree-one element is the
quotient setting that element equal to one. No flatness or domain assumption is used. -/
def degreeOneQuotientEquiv (hf : f ∈ G 1) : Away G f ≃+* (A ⧸ dehomogenizingIdeal (f := f)) where
  toFun := toQuotient G
  invFun := fromQuotient G hf
  left_inv := fromQuotient_toQuotient G hf
  right_inv := toQuotient_fromQuotient G hf
  map_mul' := map_mul (toQuotient G)
  map_add' := map_add (toQuotient G)

/-- The quotient comparison retains the actual degree-zero coefficient map. -/
theorem toQuotient_fromZero (a : G 0) :
    toQuotient G (fromZeroRingHom G (Submonoid.powers f) a) =
      Ideal.Quotient.mk (dehomogenizingIdeal (f := f)) (a : A) := by
  change IsLocalization.Away.lift f (quotient_denominator_isUnit (f := f))
    (Localization.mk (a : A) 1) = _
  rw [Localization.mk_one_eq_algebraMap, IsLocalization.Away.lift_eq]

/-- The original degree-zero ring is unchanged by dehomogenization. -/
theorem dehomogenize_fromZero (hf : f ∈ G 1) (a : G 0) :
    dehomogenize G hf a = fromZeroRingHom G (Submonoid.powers f) a := by
  apply (degreeOneQuotientEquiv G hf).injective
  exact (toQuotient_dehomogenize G hf (a : A)).trans (toQuotient_fromZero G a).symm

/-- The actual forward ring equivalence sends homogeneous fractions to their numerators. -/
@[simp]
theorem degreeOneQuotientEquiv_mk (hf : f ∈ G 1) (n : ℕ) (a : A) (ha : a ∈ G (n • 1)) :
    degreeOneQuotientEquiv G hf (Away.mk G hf n a ha) =
      Ideal.Quotient.mk (dehomogenizingIdeal (f := f)) a :=
  toQuotient_mk G hf n a ha

/-- The actual inverse ring equivalence sends a homogeneous quotient class to its fraction. -/
theorem degreeOneQuotientEquiv_symm_mk (hf : f ∈ G 1) {n : ℕ} (a : A) (ha : a ∈ G n) :
    (degreeOneQuotientEquiv G hf).symm
        (Ideal.Quotient.mk (dehomogenizingIdeal (f := f)) a) =
      Away.mk G hf n a (by simpa only [smul_eq_mul, mul_one] using ha) :=
  dehomogenize_homogeneous G hf a ha

/-- Coefficients use the original inclusion of the degree-zero ring. -/
@[simp]
theorem degreeOneQuotientEquiv_fromZero (hf : f ∈ G 1) (a : G 0) :
    degreeOneQuotientEquiv G hf (fromZeroRingHom G (Submonoid.powers f) a) =
      Ideal.Quotient.mk (dehomogenizingIdeal (f := f)) (a : A) :=
  toQuotient_fromZero G a

end HomogeneousLocalization.Away
