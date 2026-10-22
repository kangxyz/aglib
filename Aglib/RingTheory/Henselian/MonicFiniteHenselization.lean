/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.MonicFiniteReductionMaximal
public import Aglib.RingTheory.Henselian.HenselizationFiniteLocalTransport

/-!
# The closed-point monic finite henselization reduction

Monic residue equations define the actual finite polynomial action. Localizing
its base at the origin and then at the selected maximal ideal gives the original
prime-local ring. The actual henselization equivalence transports the proved
finite-local action back to that original ring's henselization. The construction
retains its literal square with the original polynomial-to-algebra map.
-/

@[expose] public section

noncomputable section

universe u v

namespace MonicFiniteReduction

variable {F : Type u} [Field F] {B : Type v} [CommRing B] [Algebra F B]
variable {n : ℕ} (z : Fin n → B) (Q : Fin n → Polynomial F)
variable (q : Ideal B) [q.IsPrime]
variable (hz : Algebra.adjoin F (Set.range z) = ⊤)
variable (hmonic : ∀ i, (Q i).Monic) (hdegree : ∀ i, 0 < (Q i).natDegree)
variable (hQ : ∀ i, Polynomial.aeval (z i) (Q i) ∈ q)

/-- The actual map from the origin's henselization to the original point's henselization. -/
def henselizedBaseMap :
    Henselization (PolynomialLocalRing F n) →+* Henselization (Localization.AtPrime q) := by
  letI := polynomialAlgebra z Q
  letI := finite z Q hz hmonic hdegree
  letI : q.IsMaximal := isMaximal z Q q hz hmonic hdegree hQ
  let p := PolynomialLocalRing.originIdeal F n
  let C := FiniteBaseLocalization.BaseLocalized (B := B) p
  let q' := FiniteBaseLocalization.selectedPrime p q
  have hq : q.comap (algebraMap (MvPolynomial (Fin n) F) B) = p :=
    comap_eq_origin z Q q hQ
  letI : q'.IsMaximal := FiniteBaseLocalization.selectedPrime_isMaximal p q hq
  exact Henselization.FiniteLocalFactor.transportedBaseMap (PolynomialLocalRing F n) C q'
    (FiniteBaseLocalization.localEquiv p q hq).toRingEquiv

/-- The exported scalar action is the literal constructed map, not an existence oracle. -/
abbrev henselizedBaseAlgebra :
    Algebra (Henselization (PolynomialLocalRing F n)) (Henselization (Localization.AtPrime q)) :=
  (henselizedBaseMap z Q q hz hmonic hdegree hQ).toAlgebra

/-- The actual original-point henselization is finite over the polynomial-origin henselization. -/
theorem finite_henselization :
    letI := henselizedBaseAlgebra z Q q hz hmonic hdegree hQ
    Module.Finite (Henselization (PolynomialLocalRing F n))
      (Henselization (Localization.AtPrime q)) := by
  let := polynomialAlgebra z Q
  let := finite z Q hz hmonic hdegree
  let : q.IsMaximal := isMaximal z Q q hz hmonic hdegree hQ
  let p := PolynomialLocalRing.originIdeal F n
  let C := FiniteBaseLocalization.BaseLocalized (B := B) p
  let q' := FiniteBaseLocalization.selectedPrime p q
  have hq : q.comap (algebraMap (MvPolynomial (Fin n) F) B) = p :=
    comap_eq_origin z Q q hQ
  let : q'.IsMaximal := FiniteBaseLocalization.selectedPrime_isMaximal p q hq
  exact Henselization.FiniteLocalFactor.finite_transport (PolynomialLocalRing F n) C q'
    (FiniteBaseLocalization.localEquiv p q hq).toRingEquiv

/-- Compatibility with the actual polynomial map before either localization or henselization. -/
theorem henselizedBaseMap_polynomial (f : MvPolynomial (Fin n) F) :
    henselizedBaseMap z Q q hz hmonic hdegree hQ
      (algebraMap (PolynomialLocalRing F n) (Henselization (PolynomialLocalRing F n))
        (algebraMap (MvPolynomial (Fin n) F) (PolynomialLocalRing F n) f)) =
    algebraMap (Localization.AtPrime q) (Henselization (Localization.AtPrime q))
      (algebraMap B (Localization.AtPrime q) (polynomialMap z Q f)) := by
  let := polynomialAlgebra z Q
  let := finite z Q hz hmonic hdegree
  let : q.IsMaximal := isMaximal z Q q hz hmonic hdegree hQ
  let p := PolynomialLocalRing.originIdeal F n
  let C := FiniteBaseLocalization.BaseLocalized (B := B) p
  let q' := FiniteBaseLocalization.selectedPrime p q
  have hq : q.comap (algebraMap (MvPolynomial (Fin n) F) B) = p :=
    comap_eq_origin z Q q hQ
  let : q'.IsMaximal := FiniteBaseLocalization.selectedPrime_isMaximal p q hq
  let e := FiniteBaseLocalization.localEquiv p q hq
  change Henselization.FiniteLocalFactor.transportedBaseMap (PolynomialLocalRing F n) C q'
    e.toRingEquiv _ = _
  rw [Henselization.FiniteLocalFactor.transportedBaseMap_algebraMap]
  congr 1
  rw [← IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) F) (PolynomialLocalRing F n)
    (Localization.AtPrime q')]
  rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) F) B (Localization.AtPrime q')]
  exact e.commutes (polynomialMap z Q f)

end MonicFiniteReduction
