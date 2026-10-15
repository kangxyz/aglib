/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.CochainComplex.HomologyZero
public import Aglib.Algebra.Homology.Simplex.Relative.Support
public import Aglib.Algebra.Homology.Simplex.Relative.Weights.Finite
public import Aglib.Algebra.Homology.Simplex.Relative.Weights.ProjectionHomology

/-!
# Original degree-zero Laurent homology in nonnegative twist degree

At nonnegative total degree, a nonempty negative support contributes no homology:
full support is impossible and proper support contracts. The original degree-zero
homology is the native polynomial monomial fiber, with original vertex coefficient
normalization. A chosen vertex is explicit; dimension zero is included.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology

universe u v

namespace MvPolynomial

variable {ι : Type v}

/-- The original empty-support weights in a natural degree are exactly the native
natural polynomial exponents in that degree. -/
def coordinatePolynomialEmptyWeightEquiv (m : ℕ) :
    {w : coordinateLaurentWeight (ι := ι) (m : ℤ) // coordinateNegativeSupport w.val = ∅} ≃
      {a : ι →₀ ℕ // a.degree = m} :=
  (coordinateEmptyWeightEquiv (m : ℤ)).trans
    ((coordinateNonnegativeDegreeExponentEquiv (m : ℤ)).symm.trans
      (Equiv.subtypeEquivRight (fun a : ι →₀ ℕ => by simp only [Int.natCast_inj])))

/-- The polynomial weight relabeling preserves the original Laurent exponent on every
supported tuple; it is exactly the original natural-exponent inclusion. -/
theorem coordinatePolynomialEmptyWeightEquiv_exponent (m : ℕ)
    (w : {w : coordinateLaurentWeight (ι := ι) (m : ℤ) // coordinateNegativeSupport w.val = ∅})
    {p : ℕ} (a : Fin (p + 1) → ι) :
    coordinateWeightExponent a w.val
        (by
          change coordinateNegativeSupport w.val.val ⊆ Set.range a
          rw [w.property]
          exact Set.empty_subset _) =
      coordinateExponentOfNat (coordinateTupleSet a)
        (coordinatePolynomialEmptyWeightEquiv m w).val := by
  apply Subtype.ext
  ext i
  change w.val.val i = ((w.val.val i).toNat : ℤ)
  exact (Int.toNat_of_nonneg
    ((coordinateNegativeSupport_eq_empty_iff w.val.val).mp w.property i)).symm

variable (R : Type u) [CommRing R]

/-- A nonempty negative support in a nonnegative degree has zero original homology in
all degrees. The full-support case is excluded by the actual negative exponent bound. -/
theorem coordinateLaurentWeightHomology_isZero_of_nonneg_degree_of_ne_empty [Finite ι]
    (m : ℕ) (w : coordinateLaurentWeight (ι := ι) (m : ℤ))
    (hw : coordinateNegativeSupport w.val ≠ ∅) (q : ℕ) :
    IsZero ((RelativeSimplex.complex R (coordinateNegativeSupport w.val)).homology q) := by
  let : Fintype ι := Fintype.ofFinite ι
  by_cases hF : coordinateNegativeSupport w.val = Set.univ
  · obtain ⟨j, _⟩ := Set.nonempty_iff_ne_empty.mpr hw
    have hcard : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨j⟩
    have hno := coordinateNegativeDegreeExponents_isEmpty (ι := ι) (m : ℤ) (by omega)
    exact (hno.false (coordinateFullWeightEquiv _ ⟨w, hF⟩)).elim
  · exact coordinateLaurentWeightHomology_isZero_of_not_endpoint R w (by tauto) q

variable [Fintype ι]

/-- Original H0 in a nonnegative Laurent degree is the native polynomial monomial module.
Only a chosen vertex and finite coordinates are needed, with independent scalar universes. -/
def coordinateLaurentTupleNonnegativeZeroWeightsEquiv (j : ι) (m : ℕ) :
    (coordinateLaurentTupleComplex (ι := ι) R (m : ℤ)).homology 0 ≃ₗ[R]
      ({a : ι →₀ ℕ // a.degree = m} →₀ R) := by
  classical
  let E := DFinsupp.subtypeDomainLinearEquiv (R := R)
    (fun w : coordinateLaurentWeight (ι := ι) (m : ℤ) => coordinateNegativeSupport w.val = ∅)
    (fun w hw => ModuleCat.subsingleton_of_isZero
      (coordinateLaurentWeightHomology_isZero_of_nonneg_degree_of_ne_empty R m w hw 0))
  let F := DFinsupp.mapRange.linearEquiv (fun w :
      {w : coordinateLaurentWeight (ι := ι) (m : ℤ) // coordinateNegativeSupport w.val = ∅} =>
    RelativeSimplex.homologyZeroLinearEquivOfEqEmpty R _ w.property j)
  let G : (Π₀ w : {w : coordinateLaurentWeight (ι := ι) (m : ℤ) //
      coordinateNegativeSupport w.val = ∅}, R) ≃ₗ[R]
        ({w : coordinateLaurentWeight (ι := ι) (m : ℤ) //
          coordinateNegativeSupport w.val = ∅} →₀ R) := (finsuppLequivDFinsupp R).symm
  exact (coordinateLaurentTupleHomologyWeightsEquiv (ι := ι) R (m : ℤ) 0).trans
    (E.trans (F.trans (G.trans (Finsupp.domLCongr (coordinatePolynomialEmptyWeightEquiv m)))))

/-- Each original polynomial coefficient is the original empty-support vertex evaluation
of the same native weight-homology component. -/
theorem coordinateLaurentTupleNonnegativeZeroWeightsEquiv_apply (j : ι) (m : ℕ)
    (x : (coordinateLaurentTupleComplex (ι := ι) R (m : ℤ)).homology 0)
    (w : {w : coordinateLaurentWeight (ι := ι) (m : ℤ) // coordinateNegativeSupport w.val = ∅}) :
    coordinateLaurentTupleNonnegativeZeroWeightsEquiv R j m x
        (coordinatePolynomialEmptyWeightEquiv m w) =
      RelativeSimplex.homologyZeroLinearEquivOfEqEmpty R _ w.property j
        (coordinateLaurentTupleHomologyWeightsEquiv R (m : ℤ) 0 x w.val) := by
  classical
  simp [coordinateLaurentTupleNonnegativeZeroWeightsEquiv, Finsupp.equivMapDomain_apply]

/-- On an original cycle, the polynomial coordinate is literally its original Laurent
coefficient on the one-vertex tuple, with the unchanged native quotient map. -/
theorem coordinateLaurentTupleNonnegativeZeroWeightsEquiv_homologyπ (j : ι) (m : ℕ)
    (c : (coordinateLaurentTupleComplex (ι := ι) R (m : ℤ)).cycles 0)
    (w : {w : coordinateLaurentWeight (ι := ι) (m : ℤ) // coordinateNegativeSupport w.val = ∅}) :
    coordinateLaurentTupleNonnegativeZeroWeightsEquiv R j m
        ((coordinateLaurentTupleComplex (ι := ι) R (m : ℤ)).homologyπ 0 c)
        (coordinatePolynomialEmptyWeightEquiv m w) =
      ((coordinateLaurentTupleComplex (ι := ι) R (m : ℤ)).iCycles 0 c (fun _ => j)).val.coeff
        (coordinateWeightExponent (fun _ : Fin 1 => j) w.val
          (by
            change coordinateNegativeSupport w.val.val ⊆ Set.range (fun _ : Fin 1 => j)
            rw [w.property]
            exact Set.empty_subset _)) := by
  rw [coordinateLaurentTupleNonnegativeZeroWeightsEquiv_apply,
    coordinateLaurentTupleHomologyWeightsEquiv_apply_eq_projection]
  have hπ := ConcreteCategory.congr_hom
    (homologyπ_naturality (coordinateLaurentWeightComplexProjection R (m : ℤ) w.val) 0) c
  change homologyMap (coordinateLaurentWeightComplexProjection R (m : ℤ) w.val) 0
      ((coordinateLaurentTupleComplex (ι := ι) R (m : ℤ)).homologyπ 0 c) =
    (RelativeSimplex.complex R (coordinateNegativeSupport w.val.val)).homologyπ 0
      (cyclesMap (coordinateLaurentWeightComplexProjection R (m : ℤ) w.val) 0 c) at hπ
  rw [hπ, RelativeSimplex.homologyZeroLinearEquivOfEqEmpty_homologyπ]
  have hi := ConcreteCategory.congr_hom
    (cyclesMap_i (coordinateLaurentWeightComplexProjection R (m : ℤ) w.val) 0) c
  change (RelativeSimplex.complex R (coordinateNegativeSupport w.val.val)).iCycles 0
      (cyclesMap (coordinateLaurentWeightComplexProjection R (m : ℤ) w.val) 0 c) =
    (coordinateLaurentWeightComplexProjection R (m : ℤ) w.val).f 0
      ((coordinateLaurentTupleComplex (ι := ι) R (m : ℤ)).iCycles 0 c) at hi
  rw [hi]
  rfl

/-- The same polynomial coordinates are literal coefficients of the canonical embedding of
original degree-zero homology into its original zero term. -/
theorem coordinateLaurentTupleNonnegativeZeroWeightsEquiv_homologyZeroι (j : ι) (m : ℕ)
    (x : (coordinateLaurentTupleComplex (ι := ι) R (m : ℤ)).homology 0)
    (w : {w : coordinateLaurentWeight (ι := ι) (m : ℤ) // coordinateNegativeSupport w.val = ∅}) :
    coordinateLaurentTupleNonnegativeZeroWeightsEquiv R j m x
        (coordinatePolynomialEmptyWeightEquiv m w) =
      (CochainComplex.homologyZeroι (coordinateLaurentTupleComplex (ι := ι) R (m : ℤ)) x
        (fun _ => j)).val.coeff
        (coordinateWeightExponent (fun _ : Fin 1 => j) w.val
          (by
            change coordinateNegativeSupport w.val.val ⊆ Set.range (fun _ : Fin 1 => j)
            rw [w.property]
            exact Set.empty_subset _)) := by
  let K := coordinateLaurentTupleComplex (ι := ι) R (m : ℤ)
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ 0)).mp (by infer_instance) x
  rw [coordinateLaurentTupleNonnegativeZeroWeightsEquiv_homologyπ]
  have h := ConcreteCategory.congr_hom (CochainComplex.homologyπ_homologyZeroι K) c
  change CochainComplex.homologyZeroι K (K.homologyπ 0 c) = K.iCycles 0 c at h
  rw [h]

end MvPolynomial
