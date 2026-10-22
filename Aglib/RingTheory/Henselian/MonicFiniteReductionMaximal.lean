/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.MonicFiniteReduction
public import Aglib.RingTheory.Henselian.FiniteBaseLocalization
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Maximality in the monic finite reduction

The actual finite polynomial action makes a prime over the polynomial origin
maximal. Its actual extension after localizing the base remains maximal, so it
satisfies the inputs of the finite-local henselization theorem.
-/

@[expose] public section

noncomputable section

universe u v

namespace MonicFiniteReduction

variable {F : Type u} [Field F] {B : Type v} [CommRing B] [Algebra F B]
variable {n : ℕ} (z : Fin n → B) (Q : Fin n → Polynomial F)

theorem isMaximal (q : Ideal B) [q.IsPrime]
    (hz : Algebra.adjoin F (Set.range z) = ⊤)
    (hmonic : ∀ i, (Q i).Monic) (hdegree : ∀ i, 0 < (Q i).natDegree)
    (hQ : ∀ i, Polynomial.aeval (z i) (Q i) ∈ q) : q.IsMaximal := by
  let := polynomialAlgebra z Q
  let := finite z Q hz hmonic hdegree
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := MvPolynomial (Fin n) F) q
  change (q.comap (polynomialMap z Q).toRingHom).IsMaximal
  rw [comap_eq_origin z Q q hQ]
  infer_instance

end MonicFiniteReduction

namespace FiniteBaseLocalization

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]

theorem selectedPrime_isMaximal (p : Ideal R) [p.IsPrime] (q : Ideal B) [q.IsMaximal]
    (hq : q.comap (algebraMap R B) = p) : (selectedPrime p q).IsMaximal :=
  IsLocalization.isMaximal_of_isMaximal_disjoint
    (Algebra.algebraMapSubmonoid B p.primeCompl) (BaseLocalized (B := B) p)
    q (disjoint_complement p q hq)

end FiniteBaseLocalization
