/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Extension.Presentation.FittingParameters

/-! # The new-side Fitting bound for arbitrary genuine polynomial parameters

Appending the actual parameter images to any finite generating family supplies
an adapted presentation. No retained minor or domain hypothesis on the new ring
is required. This is the one-sided inequality needed after a fixed-centre modification.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace KaehlerDifferential

/-- The projected Fitting ideal is contained in the original-index ideal, for
arbitrary actual polynomial parameters in a finite-type algebra. -/
theorem fittingIdeal_polynomialParameters_le
    {R B α : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Finite α] [Algebra (MvPolynomial α R) B]
    [IsScalarTower R (MvPolynomial α R) B] [Algebra.FiniteType R B]
    (k : ℕ) (hk : Nat.card α ≤ k) :
    Module.fittingIdeal B (KaehlerDifferential (MvPolynomial α R) B)
      (k - Nat.card α) ≤ Module.fittingIdeal B (KaehlerDifferential R B) k := by
  classical
  obtain ⟨n, ⟨P⟩⟩ := (Algebra.FiniteType.iff_exists_generators (R := R) (S := B)).mp
    inferInstance
  let G := P.extend (fun i : α => algebraMap (MvPolynomial α R) B (X i))
  let Q : Algebra.Presentation R B (Fin n ⊕ α) G.ker :=
    { G with relation := Subtype.val
             span_range_relation_eq_ker := by rw [Subtype.range_coe]; exact Ideal.span_eq _ }
  exact Q.fittingIdeal_absorbPolynomialParameters_le (fun _ => rfl) k hk

end KaehlerDifferential
