/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.MonicFiniteReduction

/-!
# Monic polynomial contraction over a local coefficient ring

The shared generic monic finite construction supplies the polynomial action
and its finiteness. Here its selected ideal contracts to the actual polynomial
origin over the coefficient maximal ideal, without any field hypothesis.
-/

@[expose] public section
noncomputable section
universe u v
namespace LocalMonicFiniteReduction
open MonicFiniteReduction
variable {F : Type u} [CommRing F]
variable {B : Type v} [CommRing B] [Algebra F B]
variable {n : ℕ} (z : Fin n → B) (Q : Fin n → Polynomial F)

/-- The selected ideal contracts to the actual polynomial-origin ideal. -/
theorem comap_eq_origin [IsLocalRing F] (q : Ideal B)
    (hq : q.comap (algebraMap F B) = IsLocalRing.maximalIdeal F)
    (hQ : ∀ i, Polynomial.aeval (z i) (Q i) ∈ q) :
    q.comap (polynomialMap z Q).toRingHom = PolynomialLocalRing.originIdeal F n := by
  have hmaps : (Ideal.Quotient.mk q).comp (polynomialMap z Q).toRingHom =
      (algebraMap F (B ⧸ q)).comp MvPolynomial.constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [polynomialMap]
    · intro i
      simpa [polynomialMap, Ideal.Quotient.eq_zero_iff_mem] using hQ i
  ext p
  change polynomialMap z Q p ∈ q ↔ MvPolynomial.constantCoeff p ∈ IsLocalRing.maximalIdeal F
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change ((Ideal.Quotient.mk q).comp (polynomialMap z Q).toRingHom) p = 0 ↔ _
  rw [hmaps]
  change Ideal.Quotient.mk q (algebraMap F B (MvPolynomial.constantCoeff p)) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change MvPolynomial.constantCoeff p ∈ q.comap (algebraMap F B) ↔ _
  rw [hq]

end LocalMonicFiniteReduction
