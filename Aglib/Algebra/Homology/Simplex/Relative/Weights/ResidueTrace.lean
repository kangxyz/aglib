/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.Weights.Trace
public import Aglib.Algebra.Homology.Simplex.Relative.Weights.Finite

/-!
# Bijectivity of the original Laurent residue trace

At degree minus the number of coordinates, the all-minus-one exponent is the only
all-negative weight. Nonnegative weights are impossible when there is a vertex, and
proper nonempty supports have zero native homology. The existing literal coefficient
trace is therefore bijective in the top degree, including projective dimension zero.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u

namespace MvPolynomial

variable {ι : Type u} [Fintype ι]

/-- The original all-minus-one Laurent exponent in its actual residue degree. -/
def coordinateResidueWeight : coordinateLaurentWeight (ι := ι) (-(Fintype.card ι : ℤ)) := by
  classical
  refine ⟨(coordinateNegativeProductExponent Finset.univ).val, ?_⟩
  change coordinateDegree Finset.univ (coordinateNegativeProductExponent Finset.univ) = _
  rw [coordinateDegree_negativeProduct, Finset.card_univ]

/-- Every original residue exponent coordinate is exactly minus one. -/
@[simp]
theorem coordinateResidueWeight_apply (i : ι) : (coordinateResidueWeight (ι := ι)).val i = -1 := by
  classical
  simp [coordinateResidueWeight, coordinateNegativeProductExponent]

/-- The original residue weight has full negative support. -/
theorem coordinateResidueWeight_fullSupport :
    coordinateNegativeSupport (coordinateResidueWeight (ι := ι)).val = Set.univ := by
  apply (coordinateNegativeSupport_eq_univ_iff _).mpr
  intro i
  rw [coordinateResidueWeight_apply]
  norm_num

/-- Full negative support in residue degree forces the original all-minus-one weight. -/
theorem coordinateLaurentWeight_eq_residue_of_fullSupport
    (w : coordinateLaurentWeight (ι := ι) (-(Fintype.card ι : ℤ)))
    (hw : coordinateNegativeSupport w.val = Set.univ) : w = coordinateResidueWeight := by
  let D := {a : ι →₀ ℕ // (a.degree : ℤ) = -(-(Fintype.card ι : ℤ)) - (Fintype.card ι : ℤ)}
  have hD : Subsingleton D := by
    constructor
    intro a b
    apply Subtype.ext
    have ha : a.val = 0 := (Finsupp.degree_eq_zero_iff a.val).mp (by have := a.property; omega)
    have hb : b.val = 0 := (Finsupp.degree_eq_zero_iff b.val).mp (by have := b.property; omega)
    exact ha.trans hb.symm
  let := hD
  have hfull : Subsingleton {v : coordinateLaurentWeight (ι := ι) (-(Fintype.card ι : ℤ)) //
      coordinateNegativeSupport v.val = Set.univ} :=
    ((coordinateFullWeightEquiv (-(Fintype.card ι : ℤ))).trans
      (coordinateNegativeDegreeExponentEquiv (-(Fintype.card ι : ℤ))).symm).injective.subsingleton
  exact congrArg Subtype.val
    (hfull.elim ⟨w, hw⟩ ⟨coordinateResidueWeight, coordinateResidueWeight_fullSupport⟩)

variable (R : Type u) [CommRing R]

/-- Every non-residue weight in residue degree has zero original homology in all degrees. -/
theorem coordinateLaurentWeightHomology_isZero_of_ne_residue [Nonempty ι]
    (w : coordinateLaurentWeight (ι := ι) (-(Fintype.card ι : ℤ)))
    (hw : w ≠ coordinateResidueWeight) (q : ℕ) :
    IsZero ((RelativeSimplex.complex R (coordinateNegativeSupport w.val)).homology q) := by
  by_cases hE : coordinateNegativeSupport w.val = ∅
  · have hcard : 0 < Fintype.card ι := Fintype.card_pos
    have hno := coordinateNonnegativeDegreeExponents_isEmpty (ι := ι)
      (-(Fintype.card ι : ℤ)) (by omega)
    exact (hno.false (coordinateEmptyWeightEquiv _ ⟨w, hE⟩)).elim
  · by_cases hF : coordinateNegativeSupport w.val = Set.univ
    · exact (hw (coordinateLaurentWeight_eq_residue_of_fullSupport w hF)).elim
    · exact coordinateLaurentWeightHomology_isZero_of_not_endpoint R w (by tauto) q

/-- The existing literal original-coefficient residue trace is bijective, with dimension
zero retained and the original geometric scalar universe unchanged. -/
theorem coordinateLaurentWeightTrace_residue_bijective (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    Function.Bijective (coordinateLaurentWeightTrace R n e (-(Fintype.card ι : ℤ))
      coordinateResidueWeight coordinateResidueWeight_fullSupport) := by
  classical
  let : Nonempty ι := ⟨e.symm 0⟩
  let d : ℤ := -(Fintype.card ι : ℤ)
  let w : coordinateLaurentWeight (ι := ι) d := coordinateResidueWeight
  let E := coordinateLaurentTupleHomologyWeightsEquiv (ι := ι) R d n
  let T := RelativeSimplex.topHomologyLinearEquivOfEqUnivOfEquivFin (R := R) n e
    (coordinateNegativeSupport w.val) coordinateResidueWeight_fullSupport
  have htrace (x : (coordinateLaurentTupleComplex (ι := ι) R d).homology n) :
      coordinateLaurentWeightTrace R n e d w coordinateResidueWeight_fullSupport x =
        T (E x w) := coordinateLaurentWeightTrace_eq_component R n e d w
          coordinateResidueWeight_fullSupport x
  constructor
  · intro x y h
    apply E.injective
    ext v
    by_cases hv : v = w
    · subst v
      rw [htrace, htrace] at h
      exact T.injective h
    · let := ModuleCat.subsingleton_of_isZero
        (coordinateLaurentWeightHomology_isZero_of_ne_residue R v hv n)
      exact Subsingleton.elim _ _
  · intro r
    refine ⟨E.symm (DFinsupp.single w (T.symm r)), ?_⟩
    rw [htrace]
    rw [LinearEquiv.apply_symm_apply, DFinsupp.single_eq_same, LinearEquiv.apply_symm_apply]

/-- The native residue-degree top-homology equivalence has exactly the existing original
coefficient trace as its forward linear map. -/
def coordinateLaurentResidueTraceEquiv (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    (coordinateLaurentTupleComplex (ι := ι) R (-(Fintype.card ι : ℤ))).homology n ≃ₗ[R] R :=
  LinearEquiv.ofBijective
    (coordinateLaurentWeightTrace R n e (-(Fintype.card ι : ℤ))
      coordinateResidueWeight coordinateResidueWeight_fullSupport)
    (coordinateLaurentWeightTrace_residue_bijective R n e)

/-- The residue equivalence retains the literal original trace, without a scalar renormalization. -/
theorem coordinateLaurentResidueTraceEquiv_apply (n : ℕ) (e : ι ≃ Fin (n + 1))
    (x : (coordinateLaurentTupleComplex (ι := ι) R (-(Fintype.card ι : ℤ))).homology n) :
    coordinateLaurentResidueTraceEquiv R n e x =
      coordinateLaurentWeightTrace R n e (-(Fintype.card ι : ℤ))
        coordinateResidueWeight coordinateResidueWeight_fullSupport x := rfl

end MvPolynomial
