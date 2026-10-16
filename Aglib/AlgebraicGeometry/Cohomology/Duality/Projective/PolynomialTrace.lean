/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Pairing
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.TwistMaps

/-!
# The original geometric trace of polynomial multiplication

On every original Laurent cycle, the canonical top Serre map of an actual polynomial
multiplication morphism is the coefficient of the all-minus-one monomial in the literal
product. The proof follows the original chain map, native cycle quotient, actual
cohomology map and original residue trace without replacing any of them.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory HomologicalComplex MvPolynomial
open AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u) [Fintype ι]

/-- The canonical top map of the original polynomial morphism is exactly its original
Laurent product residue on every original top cycle, with the unchanged positive sign. -/
theorem projectiveTopSerreMap_residuePolynomial_cycle (n : ℕ) (e : ι ≃ Fin (n + 1))
    (m : ℕ) (p : homogeneousSubmodule ι R m)
    (c : (coordinateLaurentTupleComplex (ι := ι) R
      (-(m : ℤ) - (Fintype.card ι : ℤ))).cycles n) :
    projectiveTopSerreMap R ι n e
        (twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ)))
        (residuePolynomialMultiplication R ι m p)
        (twistingLaurentCohomologyLinearEquiv R ι (-(m : ℤ) - (Fintype.card ι : ℤ)) n
          ((coordinateLaurentTupleComplex (ι := ι) R
            (-(m : ℤ) - (Fintype.card ι : ℤ))).homologyπ n c)) =
      (toCoordinateLaurent R (coordinateTupleSet e.symm) p.val *
        ((coordinateLaurentTupleComplex (ι := ι) R
          (-(m : ℤ) - (Fintype.card ι : ℤ))).iCycles n c e.symm).val).coeff
        (coordinateWeightExponent e.symm coordinateResidueWeight
          (fun i _ => ⟨e i, e.symm_apply_apply i⟩)) := by
  rw [projectiveTopSerreMap_apply,
    ← twistingLaurentCohomologyLinearEquiv_residuePolynomial]
  have hπ := ConcreteCategory.congr_hom
    (homologyπ_naturality (residueLaurentPolynomialMap R ι m p) n) c
  change homologyMap (residueLaurentPolynomialMap R ι m p) n
      ((coordinateLaurentTupleComplex (ι := ι) R
        (-(m : ℤ) - (Fintype.card ι : ℤ))).homologyπ n c) =
    (coordinateLaurentTupleComplex (ι := ι) R (-(Fintype.card ι : ℤ))).homologyπ n
      (cyclesMap (residueLaurentPolynomialMap R ι m p) n c) at hπ
  rw [hπ, projectiveTrace_laurent_homologyπ]
  have hi := ConcreteCategory.congr_hom
    (cyclesMap_i (residueLaurentPolynomialMap R ι m p) n) c
  change (coordinateLaurentTupleComplex (ι := ι) R (-(Fintype.card ι : ℤ))).iCycles n
      (cyclesMap (residueLaurentPolynomialMap R ι m p) n c) =
    (residueLaurentPolynomialMap R ι m p).f n
      ((coordinateLaurentTupleComplex (ι := ι) R
        (-(m : ℤ) - (Fintype.card ι : ℤ))).iCycles n c) at hi
  rw [hi, residueLaurentPolynomialMap_apply]

end AlgebraicGeometry.Scheme.Cohomology
