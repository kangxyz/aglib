# Associated primes and reducedness

Import `Aglib.RingTheory.Ideal.AssociatedPrime.Reduced`.

`Ideal.mem_of_zero_at_associated_localizations I z` applies to a
Noetherian commutative ring A and an arbitrary ideal I. If z maps to zero
in the original ring localization A_p for every associated prime p of
the actual A-module A/I, then z belongs to I.

For a nonzero quotient class, the proof chooses an associated prime
containing its annihilator. Vanishing in A_p supplies a denominator
outside p which annihilates z. That denominator also annihilates its
quotient class, a contradiction. This is the required ideal-membership
specialization of
[Stacks, Lemma 10.63.19 (0311)](https://stacks.math.columbia.edu/tag/0311).
It uses the canonical quotient and ring-localization maps directly.

`IsReduced.of_isHausdorff_of_associated_localizations x hx` assumes:

- A is Noetherian and x is a nonzerodivisor;
- A is separated for the ideal `Ideal.span {x}`, expressed by
  `IsHausdorff (Ideal.span {x}) A`;
- each ambient A_p is reduced for p associated to A/(x).

It concludes `IsReduced A`. No domain, locality, or completeness premise
is added. For a square-zero z, the preceding membership theorem writes
z = xy. Cancellation of the regular element x squared shows that y
is square-zero. Iterating puts z in every power of (x), and separation
gives z = 0. The square-zero criterion for reducedness finishes the proof.
This isolates the final algebraic argument of
[Stacks, Lemma 10.162.12 (0330)](https://stacks.math.columbia.edu/tag/0330).

`Ideal.eq_maximalIdeal_of_isReduced_quotient_of_isAssociatedPrime I`
assumes only that A is a commutative local ring, A/I is reduced, and
the maximal ideal of A is associated to the A-module A/I. It concludes
that I is the maximal ideal. Noetherianity is unnecessary here.

Mathlib's associated-prime witness presents the maximal ideal as the
radical of the annihilator of an element u in A/I. That element is
nonzero. A representative of u in the maximal ideal would make a power
of u zero, contrary to reducedness. Hence the representative is a unit.
Its quotient image is a unit as well. An element in the radical of its
annihilator has nilpotent image in A/I, and therefore lies in I. The
opposite containment follows because I annihilates u. The actual quotient
is consequently the residue-field quotient.

The current consumer is the associated-prime criterion for reducedness
of a completed local ring in the bounded Nagata surface argument. Its
regularity hypothesis concerns ambient local rings, such as R_p or
(completion R)_q. This module does not assume regularity of a localized
principal quotient. The last theorem derives a residue-field quotient
only after its reducedness and associated-maximal-ideal premises have
been established.

The flat associated-prime base-change theorem, the actual local
completion comparisons, and the finite semilocal completion argument
remain separate obligations. These lemmas do not prove that arbitrary
completions are reduced, that nonnormal complete surfaces have finite
normalization, or that arbitrary finite-type algebras are Nagata.
