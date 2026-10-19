/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Flat.PrincipalQuotient.Fibrewise

/-!
# Regular equations at one prime from one fiber

`Algebra.isSMulRegular_atPrime_of_fiber_regular`: for a flat finitely presented algebra `S`
over an arbitrary commutative ring `R`, an element `a` whose image `1 ⊗ a` is regular on the
fibre `(q.under R).Fiber S` is regular in the local ring of `S` at `q`. This is the
localized-base form of the proved local criterion
`Algebra.FlatApproximation.regular_and_flat_at_prime_of_residue_regular`, as in the proof of
`Algebra.regular_and_flat_of_fibre_regular`, but using only the one fibre through `q`.

The consumer is the pointwise fibre criterion for relative effective Cartier divisors
(Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Lemma 3.4, pp. 22-23).
-/

@[expose] public section

noncomputable section
open TensorProduct

section Ring

/-- Fibrewise regularity of `1 ⊗ a` over the image of a prime gives regularity of `a` at that
prime, for a flat finitely presented algebra over an arbitrary base. -/
theorem Algebra.isSMulRegular_atPrime_of_fiber_regular {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] [Module.Flat R S] (a : S)
    (q : Ideal S) [q.IsPrime]
    (ha : IsSMulRegular ((q.under R).Fiber S) ((1 : (q.under R).ResidueField) ⊗ₜ[R] a)) :
    IsSMulRegular (Localization.AtPrime q) (algebraMap S (Localization.AtPrime q) a) := by
  refine (Algebra.regular_and_flat_atPrime_of_localizedBase (R := R) q a ?_).1
  intro Q hQ hQover
  let := hQover
  exact Algebra.FlatApproximation.regular_and_flat_at_prime_of_residue_regular
    ((1 : Localization.AtPrime (q.under R)) ⊗ₜ[R] a)
    (Algebra.residue_regular_localized_base (q.under R) a ha) Q

end Ring
