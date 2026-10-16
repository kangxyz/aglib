/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.Support
public import Aglib.Algebra.Homology.Simplex.Relative.Weights.Finite

/-!
# Original scalar coefficients of the endpoint Laurent cohomology

In positive projective dimension, H0 is the original nonnegative monomial
degree fiber and top cohomology is the original all-negative degree fiber.
The comparisons restrict the actual weight homology sum and apply the native
vertex or increasing-tuple scalar comparisons, preserving their normalizations.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology

universe u

namespace MvPolynomial

variable (R : Type u) [CommRing R]

/-- In positive projective dimension only full negative support can contribute
to the original top homology. -/
theorem coordinateLaurentWeightHomology_isZero_top_of_ne_full (n : ℕ) (d : ℤ)
    (hn : n ≠ 0) (e : coordinateLaurentWeight (ι := Fin (n + 1)) d)
    (he : coordinateNegativeSupport e.val ≠ Set.univ) :
    IsZero ((RelativeSimplex.complex R (coordinateNegativeSupport e.val)).homology n) := by
  by_cases hE : coordinateNegativeSupport e.val = ∅
  · rw [hE]
    cases n with
    | zero => exact (hn rfl).elim
    | succ n => exact (RelativeSimplex.exactAt_succ_of_not_mem (R := R)
        (S := (∅ : Set (Fin (n + 2)))) (0 : Fin (n + 2)) (by simp) n).isZero_homology
  · exact coordinateLaurentWeightHomology_isZero_of_not_endpoint R e (by tauto) n

/-- In positive projective dimension only empty negative support can contribute
to original degree-zero homology. -/
theorem coordinateLaurentWeightHomology_isZero_zero_of_ne_empty (n : ℕ) (d : ℤ)
    (hn : n ≠ 0) (e : coordinateLaurentWeight (ι := Fin (n + 1)) d)
    (he : coordinateNegativeSupport e.val ≠ ∅) :
    IsZero ((RelativeSimplex.complex R (coordinateNegativeSupport e.val)).homology 0) := by
  by_cases hF : coordinateNegativeSupport e.val = Set.univ
  · rw [hF]
    exact RelativeSimplex.fullSupport_isZero_homology_of_ne n 0 (Ne.symm hn)
  · exact coordinateLaurentWeightHomology_isZero_of_not_endpoint R e (by tauto) 0

/-- Original top Laurent cohomology is the native finitely supported scalar
module on the all-negative degree fiber, in positive projective dimension. -/
def coordinateLaurentTupleTopWeightsEquiv (n : ℕ) (d : ℤ) (hn : n ≠ 0) :
    (coordinateLaurentTupleComplex (ι := Fin (n + 1)) R d).homology n ≃ₗ[R]
      (coordinateNegativeDegreeExponents (ι := Fin (n + 1)) d →₀ R) := by
  classical
  let E := DFinsupp.subtypeDomainLinearEquiv (R := R)
    (fun e : coordinateLaurentWeight (ι := Fin (n + 1)) d =>
      coordinateNegativeSupport e.val = Set.univ)
    (fun e he => ModuleCat.subsingleton_of_isZero
      (coordinateLaurentWeightHomology_isZero_top_of_ne_full R n d hn e he))
  let F := DFinsupp.mapRange.linearEquiv (fun e :
      {e : coordinateLaurentWeight (ι := Fin (n + 1)) d //
        coordinateNegativeSupport e.val = Set.univ} =>
    RelativeSimplex.topHomologyLinearEquivOfEqUniv R n _ e.property)
  let G : (Π₀ e : {e : coordinateLaurentWeight (ι := Fin (n + 1)) d //
      coordinateNegativeSupport e.val = Set.univ}, R) ≃ₗ[R]
        ({e : coordinateLaurentWeight (ι := Fin (n + 1)) d //
          coordinateNegativeSupport e.val = Set.univ} →₀ R) := (finsuppLequivDFinsupp R).symm
  exact (coordinateLaurentTupleHomologyWeightsEquiv (ι := Fin (n + 1)) R d n).trans
    (E.trans (F.trans (G.trans (Finsupp.domLCongr (coordinateFullWeightEquiv d)))))

/-- Original H0 Laurent cohomology is the native polynomial monomial degree
fiber, in positive projective dimension and arbitrary integer degree. -/
def coordinateLaurentTupleZeroWeightsEquiv (n : ℕ) (d : ℤ) (hn : n ≠ 0) :
    (coordinateLaurentTupleComplex (ι := Fin (n + 1)) R d).homology 0 ≃ₗ[R]
      ({a : Fin (n + 1) →₀ ℕ // (a.degree : ℤ) = d} →₀ R) := by
  classical
  let E := DFinsupp.subtypeDomainLinearEquiv (R := R)
    (fun e : coordinateLaurentWeight (ι := Fin (n + 1)) d =>
      coordinateNegativeSupport e.val = ∅)
    (fun e he => ModuleCat.subsingleton_of_isZero
      (coordinateLaurentWeightHomology_isZero_zero_of_ne_empty R n d hn e he))
  let F := DFinsupp.mapRange.linearEquiv (fun e :
      {e : coordinateLaurentWeight (ι := Fin (n + 1)) d //
        coordinateNegativeSupport e.val = ∅} =>
    RelativeSimplex.homologyZeroLinearEquivOfEqEmpty R _ e.property (0 : Fin (n + 1)))
  let G : (Π₀ e : {e : coordinateLaurentWeight (ι := Fin (n + 1)) d //
      coordinateNegativeSupport e.val = ∅}, R) ≃ₗ[R]
        ({e : coordinateLaurentWeight (ι := Fin (n + 1)) d //
          coordinateNegativeSupport e.val = ∅} →₀ R) := (finsuppLequivDFinsupp R).symm
  exact (coordinateLaurentTupleHomologyWeightsEquiv (ι := Fin (n + 1)) R d 0).trans
    (E.trans (F.trans (G.trans (Finsupp.domLCongr
      ((coordinateEmptyWeightEquiv d).trans (coordinateNonnegativeDegreeExponentEquiv d).symm)))))

/-- The top comparison uses the original weight homology coefficient and its
native increasing-tuple normalization. -/
theorem coordinateLaurentTupleTopWeightsEquiv_apply (n : ℕ) (d : ℤ) (hn : n ≠ 0)
    (x : (coordinateLaurentTupleComplex (ι := Fin (n + 1)) R d).homology n)
    (e : {e : coordinateLaurentWeight (ι := Fin (n + 1)) d //
      coordinateNegativeSupport e.val = Set.univ}) :
    coordinateLaurentTupleTopWeightsEquiv R n d hn x (coordinateFullWeightEquiv d e) =
      RelativeSimplex.topHomologyLinearEquivOfEqUniv R n _ e.property
        (coordinateLaurentTupleHomologyWeightsEquiv R d n x e.val) := by
  classical
  simp [coordinateLaurentTupleTopWeightsEquiv, Finsupp.equivMapDomain_apply]

/-- The H0 comparison uses the original weight homology coefficient and native
vertex evaluation, followed by the original natural exponent cast. -/
theorem coordinateLaurentTupleZeroWeightsEquiv_apply (n : ℕ) (d : ℤ) (hn : n ≠ 0)
    (x : (coordinateLaurentTupleComplex (ι := Fin (n + 1)) R d).homology 0)
    (e : {e : coordinateLaurentWeight (ι := Fin (n + 1)) d //
      coordinateNegativeSupport e.val = ∅}) :
    coordinateLaurentTupleZeroWeightsEquiv R n d hn x
        ((coordinateNonnegativeDegreeExponentEquiv d).symm (coordinateEmptyWeightEquiv d e)) =
      RelativeSimplex.homologyZeroLinearEquivOfEqEmpty R _ e.property (0 : Fin (n + 1))
        (coordinateLaurentTupleHomologyWeightsEquiv R d 0 x e.val) := by
  classical
  simp [coordinateLaurentTupleZeroWeightsEquiv, Finsupp.equivMapDomain_apply]

end MvPolynomial
