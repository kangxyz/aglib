/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.MonicFiniteHenselization

/-!
# An actual common-universe finite origin model

The model is the selected local factor of the actual tensor product with the
polynomial-origin henselization. Unlike the original prime localization, this
model lives in the maximum of the coefficient and source universes. When the
coefficient field already occupies that common universe, as in the geometric
parameter reduction, the same-universe approximation theorem applies. The
ring equivalence back to the original henselization is constructed from the
proved localization and henselization equivalences.
-/

@[expose] public section

noncomputable section

universe u v

namespace MonicFiniteReduction

variable {F : Type u} [Field F] {B : Type v} [CommRing B] [Algebra F B]
variable {n : ℕ} (z : Fin n → B) (Q : Fin n → Polynomial F)

/-- Construct the actual finite local tensor factor, retaining the universe bound. -/
theorem exists_finite_origin_model (q : Ideal B) [q.IsPrime]
    (hz : Algebra.adjoin F (Set.range z) = ⊤)
    (hmonic : ∀ i, (Q i).Monic) (hdegree : ∀ i, 0 < (Q i).natDegree)
    (hQ : ∀ i, Polynomial.aeval (z i) (Q i) ∈ q) :
    ∃ (A : Type (max u v)) (_ : CommRing A)
      (_ : Algebra (Henselization (PolynomialLocalRing F n)) A)
      (_ : Module.Finite (Henselization (PolynomialLocalRing F n)) A) (_ : IsLocalRing A),
      Nonempty (Henselization (Localization.AtPrime q) ≃+* A) := by
  let := polynomialAlgebra z Q
  let := finite z Q hz hmonic hdegree
  let : q.IsMaximal := isMaximal z Q q hz hmonic hdegree hQ
  let p := PolynomialLocalRing.originIdeal F n
  let C := FiniteBaseLocalization.BaseLocalized (B := B) p
  let q' := FiniteBaseLocalization.selectedPrime p q
  have hq : q.comap (algebraMap (MvPolynomial (Fin n) F) B) = p :=
    comap_eq_origin z Q q hQ
  let : q'.IsMaximal := FiniteBaseLocalization.selectedPrime_isMaximal p q hq
  let A := Henselization.FiniteLocalFactor.SelectedRing (PolynomialLocalRing F n) C q'
  let e := FiniteBaseLocalization.localEquiv p q hq
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨(Henselization.equivOfRingEquiv e.toRingEquiv).symm.trans
    (Henselization.FiniteLocalFactor.equiv (PolynomialLocalRing F n) C q').toRingEquiv⟩

end MonicFiniteReduction
