/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.PolynomialTrace
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.NegativeTwists
public import Aglib.AlgebraicGeometry.Cohomology.Duality.LaurentPairing.Pairing

/-!
# Original monomial traces and the native residue pairing

The complementary exponent `-1-a` turns the canonical geometric trace of multiplication
by a polynomial basis monomial into its original negative Laurent coefficient. This is
exactly the existing native residue pairing, with all original cycle and section maps.
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

/-- Every residue-pair source degree is negative, including projective dimension zero. -/
theorem residueTwistDegree_neg (n : ℕ) (e : ι ≃ Fin (n + 1)) (m : ℕ) :
    -(m : ℤ) - (Fintype.card ι : ℤ) < 0 := by
  have hcard := Fintype.card_congr e
  simp only [Fintype.card_fin] at hcard
  omega

/-- The original negative-piece cohomology comparison in exactly the degree paired with
homogeneous polynomials of degree `m` by the existing native residue pairing. -/
def residueTwistCohomologyLinearEquiv (n : ℕ) (e : ι ≃ Fin (n + 1)) (m : ℕ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
      (twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ))) n
    Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
      (twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ)))) n ≃ₗ[R]
        coordinateNegativePiece (ι := ι) R (-(m : ℤ) - (Fintype.card ι : ℤ)) :=
  twistingNegativeTopCohomologyLinearEquiv R ι n e _ (residueTwistDegree_neg ι n e m)

/-- On an original cycle and an original polynomial basis monomial, the canonical top map
is exactly the existing native Laurent residue pairing. -/
theorem projectiveTopSerreMap_residueMonomial_cycle (n : ℕ) (e : ι ≃ Fin (n + 1))
    (m : ℕ) (a : {a : ι →₀ ℕ // a.degree = m})
    (c : (coordinateLaurentTupleComplex (ι := ι) R
      (-(m : ℤ) - (Fintype.card ι : ℤ))).cycles n) :
    projectiveTopSerreMap R ι n e
        (twistingSheaf R ι (-(m : ℤ) - (Fintype.card ι : ℤ)))
        (residuePolynomialMultiplication R ι m (homogeneousPieceBasis R m a))
        (twistingLaurentCohomologyLinearEquiv R ι (-(m : ℤ) - (Fintype.card ι : ℤ)) n
          ((coordinateLaurentTupleComplex (ι := ι) R
            (-(m : ℤ) - (Fintype.card ι : ℤ))).homologyπ n c)) =
      coordinateLaurentResiduePairing R m (homogeneousPieceBasis R m a)
        (residueTwistCohomologyLinearEquiv R ι n e m
          (twistingLaurentCohomologyLinearEquiv R ι (-(m : ℤ) - (Fintype.card ι : ℤ)) n
            ((coordinateLaurentTupleComplex (ι := ι) R
              (-(m : ℤ) - (Fintype.card ι : ℤ))).homologyπ n c))) := by
  let d : ℤ := -(m : ℤ) - (Fintype.card ι : ℤ)
  let β := coordinateHomogeneousNegativeExponentEquiv (ι := ι) m a
  let w : {w : coordinateLaurentWeight (ι := ι) d //
      coordinateNegativeSupport w.val = Set.univ} := (coordinateFullWeightEquiv d).symm β
  let v := coordinateWeightExponent e.symm w.val (fun i _ => ⟨e i, e.symm_apply_apply i⟩)
  let z := coordinateWeightExponent e.symm (coordinateResidueWeight (ι := ι))
    (fun i _ => ⟨e i, e.symm_apply_apply i⟩)
  have hsum : coordinateExponentOfNat (coordinateTupleSet e.symm) a.val + v = z := by
    apply Subtype.ext
    ext k
    change (a.val k : ℤ) + (coordinateNegativeComplement a.val).val k =
      (coordinateResidueWeight (ι := ι)).val k
    rw [coordinateNegativeComplement_apply, coordinateResidueWeight_apply]
    omega
  have hcoeff := twistingNegativeTopCohomologyLinearEquiv_laurent_homologyπ_coeff
    R ι n e d (residueTwistDegree_neg ι n e m) c w
  change (residueTwistCohomologyLinearEquiv R ι n e m
      (twistingLaurentCohomologyLinearEquiv R ι d n
        ((coordinateLaurentTupleComplex (ι := ι) R d).homologyπ n c))).val.coeff
        (coordinateNegativeComplement a.val) =
    ((coordinateLaurentTupleComplex (ι := ι) R d).iCycles n c e.symm).val.coeff v at hcoeff
  rw [projectiveTopSerreMap_residuePolynomial_cycle, coordinateLaurentResiduePairing_apply,
    homogeneousPieceBasis_val, toCoordinateLaurent_monomial]
  change (AddMonoidAlgebra.single (coordinateExponentOfNat (coordinateTupleSet e.symm) a.val) 1 *
      ((coordinateLaurentTupleComplex (ι := ι) R d).iCycles n c e.symm).val).coeff z = _
  rw [← hsum, AddMonoidAlgebra.coeff_single_mul_add, one_mul]
  rw [toCoordinateLaurent_monomial, ← coordinateExponentOfNat_add_negativeComplement a.val,
    AddMonoidAlgebra.coeff_single_mul_add, one_mul]
  exact hcoeff.symm

end AlgebraicGeometry.Scheme.Cohomology
