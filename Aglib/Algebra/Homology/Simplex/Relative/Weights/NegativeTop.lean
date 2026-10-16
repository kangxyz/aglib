/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.Weights.Trace
public import Aglib.Algebra.Homology.Simplex.Relative.Weights.Finite

/-!
# Original top Laurent homology in negative degree

In negative total degree, nonnegative weights are impossible. Every non-full weight
therefore has proper nonempty negative support and zero native homology. The original
top homology is consequently the native scalar Finsupp on all-negative exponents. The
comparison works in arbitrary geometric universes and includes dimension zero; its
coefficients are exactly the existing original Laurent weight traces.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u

namespace MvPolynomial

variable {ι : Type u} (R : Type u) [CommRing R]

/-- A non-full negative-support weight of negative total degree has zero original homology
in every degree, because its support is nonempty and proper. -/
theorem coordinateLaurentWeightHomology_isZero_of_neg_degree_of_ne_full
    (d : ℤ) (hd : d < 0) (w : coordinateLaurentWeight (ι := ι) d)
    (hw : coordinateNegativeSupport w.val ≠ Set.univ) (q : ℕ) :
    IsZero ((RelativeSimplex.complex R (coordinateNegativeSupport w.val)).homology q) := by
  by_cases hE : coordinateNegativeSupport w.val = ∅
  · have hno := coordinateNonnegativeDegreeExponents_isEmpty (ι := ι) d hd
    exact (hno.false (coordinateEmptyWeightEquiv d ⟨w, hE⟩)).elim
  · exact coordinateLaurentWeightHomology_isZero_of_not_endpoint R w (by tauto) q

/-- Original Laurent homology in negative total degree vanishes away from its top degree.
The empty-support part is impossible, so this includes degree zero without a shortcut. -/
theorem coordinateLaurentTupleHomology_isZero_of_neg_degree_of_ne_top
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℤ) (hd : d < 0) (q : ℕ) (hq : q ≠ n) :
    IsZero ((coordinateLaurentTupleComplex (ι := ι) R d).homology q) := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  apply ModuleCat.isZero_iff_subsingleton.mpr
  constructor
  intro x y
  apply (coordinateLaurentTupleHomologyWeightsEquiv (ι := ι) R d q).injective
  ext w
  have hz : IsZero ((RelativeSimplex.complex R
      (coordinateNegativeSupport w.val)).homology q) := by
    by_cases hw : coordinateNegativeSupport w.val = Set.univ
    · rw [hw]
      exact RelativeSimplex.fullSupport_isZero_homology_of_ne_of_equivFin n e q hq
    · exact coordinateLaurentWeightHomology_isZero_of_neg_degree_of_ne_full R d hd w hw q
  exact (ModuleCat.subsingleton_of_isZero hz).elim _ _

variable [Fintype ι]

/-- Original top Laurent homology in any negative degree is the scalar Finsupp on its
original all-negative exponent fiber, including projective dimension zero. -/
def coordinateLaurentTupleNegativeTopWeightsEquiv (n : ℕ) (e : ι ≃ Fin (n + 1))
    (d : ℤ) (hd : d < 0) :
    (coordinateLaurentTupleComplex (ι := ι) R d).homology n ≃ₗ[R]
      (coordinateNegativeDegreeExponents (ι := ι) d →₀ R) := by
  classical
  let E := DFinsupp.subtypeDomainLinearEquiv (R := R)
    (fun w : coordinateLaurentWeight (ι := ι) d => coordinateNegativeSupport w.val = Set.univ)
    (fun w hw => ModuleCat.subsingleton_of_isZero
      (coordinateLaurentWeightHomology_isZero_of_neg_degree_of_ne_full R d hd w hw n))
  let F := DFinsupp.mapRange.linearEquiv (fun w :
      {w : coordinateLaurentWeight (ι := ι) d // coordinateNegativeSupport w.val = Set.univ} =>
    RelativeSimplex.topHomologyLinearEquivOfEqUnivOfEquivFin (R := R) n e _ w.property)
  let G : (Π₀ w : {w : coordinateLaurentWeight (ι := ι) d //
      coordinateNegativeSupport w.val = Set.univ}, R) ≃ₗ[R]
        ({w : coordinateLaurentWeight (ι := ι) d //
          coordinateNegativeSupport w.val = Set.univ} →₀ R) := (finsuppLequivDFinsupp R).symm
  exact (coordinateLaurentTupleHomologyWeightsEquiv (ι := ι) R d n).trans
    (E.trans (F.trans (G.trans (Finsupp.domLCongr (coordinateFullWeightEquiv d)))))

/-- Every coefficient of the comparison is exactly the existing original Laurent weight
trace on the same homology class. -/
theorem coordinateLaurentTupleNegativeTopWeightsEquiv_apply (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (d : ℤ) (hd : d < 0)
    (x : (coordinateLaurentTupleComplex (ι := ι) R d).homology n)
    (w : {w : coordinateLaurentWeight (ι := ι) d //
      coordinateNegativeSupport w.val = Set.univ}) :
    coordinateLaurentTupleNegativeTopWeightsEquiv R n e d hd x (coordinateFullWeightEquiv d w) =
      coordinateLaurentWeightTrace R n e d w.val w.property x := by
  classical
  rw [coordinateLaurentWeightTrace_eq_component]
  simp [coordinateLaurentTupleNegativeTopWeightsEquiv, Finsupp.equivMapDomain_apply]

/-- On an original cycle, these coefficients are the literal original Laurent coefficients
on the enumerated tuple, with the original quotient and positive sign. -/
theorem coordinateLaurentTupleNegativeTopWeightsEquiv_homologyπ (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (d : ℤ) (hd : d < 0)
    (c : (coordinateLaurentTupleComplex (ι := ι) R d).cycles n)
    (w : {w : coordinateLaurentWeight (ι := ι) d //
      coordinateNegativeSupport w.val = Set.univ}) :
    coordinateLaurentTupleNegativeTopWeightsEquiv R n e d hd
        ((coordinateLaurentTupleComplex (ι := ι) R d).homologyπ n c)
        (coordinateFullWeightEquiv d w) =
      ((coordinateLaurentTupleComplex (ι := ι) R d).iCycles n c e.symm).val.coeff
        (coordinateWeightExponent e.symm w.val (fun i _ => ⟨e i, e.symm_apply_apply i⟩)) := by
  rw [coordinateLaurentTupleNegativeTopWeightsEquiv_apply]
  exact coordinateLaurentWeightTrace_homologyπ R n e d w.val w.property c

end MvPolynomial
