/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.FiniteReindex
public import Aglib.Algebra.Homology.Simplex.Relative.Weights.Finite

/-!
# Finite Laurent cohomology on geometric coordinate types

The scalar ring and finite coordinate type may share any universe. A displayed
enumeration by `Fin (n + 1)` supplies native full-support homology comparisons
through small-target reindexing. The unchanged raw tuple complex therefore has
finite free native homology and the same endpoint and sharp degree bounds,
without identifying the large coordinate type with a small type by equality.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology

universe u

namespace MvPolynomial

variable {ι : Type u} (R : Type u) [CommRing R]

/-- Every original weight has finite free homology for an enumerated finite
geometric coordinate type, preserving the arbitrary scalar universe. -/
theorem coordinateLaurentWeightHomology_finite_free_of_equivFin
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ) (q : ℕ)
    (w : coordinateLaurentWeight (ι := ι) d) :
    Module.Finite R ((RelativeSimplex.complex R (coordinateNegativeSupport w.val)).homology q) ∧
      Module.Free R ((RelativeSimplex.complex R (coordinateNegativeSupport w.val)).homology q) := by
  by_cases hE : coordinateNegativeSupport w.val = ∅
  · rw [hE]
    cases q with
    | zero =>
      exact ⟨Module.Finite.equiv (RelativeSimplex.emptySupportHomologyZeroLinearEquiv
        (R := R) (e.symm 0) |>.symm), Module.Free.of_equiv
          (RelativeSimplex.emptySupportHomologyZeroLinearEquiv (R := R) (e.symm 0) |>.symm)⟩
    | succ q =>
      let := ModuleCat.subsingleton_of_isZero
        (RelativeSimplex.exactAt_succ_of_not_mem (R := R) (S := (∅ : Set ι))
          (e.symm 0) (by simp) q).isZero_homology
      exact ⟨inferInstance, inferInstance⟩
  · by_cases hF : coordinateNegativeSupport w.val = Set.univ
    · rw [hF]
      by_cases hq : q = n
      · subst q
        exact ⟨Module.Finite.equiv
          (RelativeSimplex.fullSupportTopLinearEquivOfEquivFin (R := R) n e).symm,
          Module.Free.of_equiv
            (RelativeSimplex.fullSupportTopLinearEquivOfEquivFin (R := R) n e).symm⟩
      · let := ModuleCat.subsingleton_of_isZero
          (RelativeSimplex.fullSupport_isZero_homology_of_ne_of_equivFin (R := R) n e q hq)
        exact ⟨inferInstance, inferInstance⟩
    · let := ModuleCat.subsingleton_of_isZero
        (coordinateLaurentWeightHomology_isZero_of_not_endpoint R w (by tauto) q)
      exact ⟨inferInstance, inferInstance⟩

/-- The original raw Laurent homology is free for arbitrary finite geometric
coordinate types with the displayed enumeration. -/
theorem coordinateLaurentTupleHomology_free_of_equivFin
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ) (q : ℕ) :
    Module.Free R ((coordinateLaurentTupleComplex (ι := ι) R d).homology q) := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  let : ∀ w : coordinateLaurentWeight (ι := ι) d,
      Module.Free R ((RelativeSimplex.complex R (coordinateNegativeSupport w.val)).homology q) :=
    fun w => (coordinateLaurentWeightHomology_finite_free_of_equivFin R n e d q w).2
  exact Module.Free.of_equiv (coordinateLaurentTupleHomologyWeightsEquiv (ι := ι) R d q).symm

/-- Finiteness of the unchanged raw homology, through its actual finite
empty/full-support weight set, in the arbitrary geometric scalar universe. -/
theorem coordinateLaurentTupleHomology_finite_of_equivFin
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ) (q : ℕ) :
    Module.Finite R ((coordinateLaurentTupleComplex (ι := ι) R d).homology q) := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  let : ∀ w : coordinateLaurentEndpointWeight (ι := ι) d,
      Module.Finite R
        ((RelativeSimplex.complex R (coordinateNegativeSupport w.val.val)).homology q) :=
    fun w => (coordinateLaurentWeightHomology_finite_free_of_equivFin R n e d q w.val).1
  exact Module.Finite.equiv (coordinateLaurentTupleHomologyEndpointEquiv (ι := ι) R d q).symm

/-- Each actual weight vanishes away from the two possible endpoint degrees
for an arbitrary finite geometric coordinate type. -/
theorem coordinateLaurentWeightHomology_isZero_of_ne_endpoints_of_equivFin
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ) (q : ℕ) (hq0 : q ≠ 0) (hqn : q ≠ n)
    (w : coordinateLaurentWeight (ι := ι) d) :
    IsZero ((RelativeSimplex.complex R (coordinateNegativeSupport w.val)).homology q) := by
  by_cases hE : coordinateNegativeSupport w.val = ∅
  · rw [hE]
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
    exact (RelativeSimplex.exactAt_succ_of_not_mem (R := R) (S := (∅ : Set ι))
      (e.symm 0) (by simp) q).isZero_homology
  · by_cases hF : coordinateNegativeSupport w.val = Set.univ
    · rw [hF]
      exact RelativeSimplex.fullSupport_isZero_homology_of_ne_of_equivFin n e q hqn
    · exact coordinateLaurentWeightHomology_isZero_of_not_endpoint R w (by tauto) q

/-- The unchanged raw homology vanishes outside zero and the projective top
degree, for arbitrary finite geometric coordinate types. -/
theorem coordinateLaurentTupleHomology_isZero_of_ne_endpoints_of_equivFin
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ) (q : ℕ) (hq0 : q ≠ 0) (hqn : q ≠ n) :
    IsZero ((coordinateLaurentTupleComplex (ι := ι) R d).homology q) := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  apply ModuleCat.isZero_iff_subsingleton.mpr
  constructor
  intro x y
  apply (coordinateLaurentTupleHomologyWeightsEquiv (ι := ι) R d q).injective
  ext w
  exact (ModuleCat.subsingleton_of_isZero
    (coordinateLaurentWeightHomology_isZero_of_ne_endpoints_of_equivFin R n e d q
      hq0 hqn w)).elim _ _

/-- The sharp bound `d ≥ -n` kills all positive homology of every actual
weight, in the unchanged geometric coefficient universe. -/
theorem coordinateLaurentWeightHomology_isZero_of_neg_le_degree_of_equivFin
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ) (q : ℕ) (hd : -(n : ℤ) ≤ d) (hq : q ≠ 0)
    (w : coordinateLaurentWeight (ι := ι) d) :
    IsZero ((RelativeSimplex.complex R (coordinateNegativeSupport w.val)).homology q) := by
  by_cases hE : coordinateNegativeSupport w.val = ∅
  · rw [hE]
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
    exact (RelativeSimplex.exactAt_succ_of_not_mem (R := R) (S := (∅ : Set ι))
      (e.symm 0) (by simp) q).isZero_homology
  · by_cases hF : coordinateNegativeSupport w.val = Set.univ
    · let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
      have hc : Fintype.card ι = n + 1 := (Fintype.card_congr e).trans (Fintype.card_fin _)
      have hz := coordinateNegativeDegreeExponents_isEmpty (ι := ι) d (by
        rw [hc]
        simp only [Nat.cast_add, Nat.cast_one]
        omega)
      exact (hz.false (coordinateFullWeightEquiv d ⟨w, hF⟩)).elim
    · exact coordinateLaurentWeightHomology_isZero_of_not_endpoint R w (by tauto) q

/-- Sharp positive-degree vanishing for the original raw complex over any
scalar universe and finite geometric coordinate enumeration. -/
theorem coordinateLaurentTupleHomology_isZero_of_neg_le_degree_of_equivFin
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ) (q : ℕ) (hd : -(n : ℤ) ≤ d) (hq : q ≠ 0) :
    IsZero ((coordinateLaurentTupleComplex (ι := ι) R d).homology q) := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  apply ModuleCat.isZero_iff_subsingleton.mpr
  constructor
  intro x y
  apply (coordinateLaurentTupleHomologyWeightsEquiv (ι := ι) R d q).injective
  ext w
  exact (ModuleCat.subsingleton_of_isZero
    (coordinateLaurentWeightHomology_isZero_of_neg_le_degree_of_equivFin R n e d q
      hd hq w)).elim _ _

end MvPolynomial
