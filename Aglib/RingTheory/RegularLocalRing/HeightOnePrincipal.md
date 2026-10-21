# Principal height-one primes in low-dimensional regular local rings

[HeightOnePrincipal.lean](HeightOnePrincipal.lean) uses Mathlib's actual
`IsRegularLocalRing R`, `ringKrullDim R`, and ideals `p : Ideal R`. Regular
locality already includes the Noetherian and local conditions. Domainness is a
proved consequence, rather than an additional assumption.

The principal result is
`IsRegularLocalRing.isPrincipal_of_prime_ne_maximalIdeal_of_dimension_two`.
It assumes `ringKrullDim R = 2`, `p.IsPrime`, and
`p ≠ IsLocalRing.maximalIdeal R`, and concludes `p.IsPrincipal`. It includes
`p = ⊥`. The companion
`IsRegularLocalRing.isPrincipal_of_height_eq_one_of_dimension_le_two` assumes
`ringKrullDim R ≤ 2` and `p.height = 1` and concludes the same statement.

`IsRegularLocalRing.primeIdealBasisOfDimensionTwo` gives a
`Basis PUnit R p` when the nonmaximal prime is nonzero.
`IsRegularLocalRing.heightOneIdealBasisOfDimensionLETwo` gives the same basis
for a height-one prime in dimension at most two; nonvanishing is derived.
These are bases on the actual ideal subtype. Their map into `R` is the usual
linear inclusion `p.subtype`. No auxiliary ideal or unidentified isomorphic
module replaces `p`.

The argument uses two applications of Nakayama's lemma. Write `m` for the
maximal ideal. For a nonmaximal prime `p`, the containment
`m ≤ p ⊔ m²` would give `m ≤ p` by Nakayama on the finitely generated maximal
ideal modulo `p`. Since `p ≤ m`, this would force `p = m`. There is therefore
an element `x ∈ m` outside `p ⊔ m²`, so `x ∉ p` and `x ∉ m²`.

The existing parameter-quotient theorem makes `Q = R/(x)` regular local of
dimension one. The existing regular-local domain theorem and Mathlib's
principal-ideal characterization in cotangent dimension at most one show that
every ideal of `Q` is principal. Let `q : R →+* Q` be the canonical quotient
map. The generator of `p.map q` lies in its image, so surjectivity of `q` lifts
it to an element `b ∈ p`.

For every `a ∈ p`, lift the coefficient expressing `q(a)` as a multiple of
`q(b)`. Then `a - cb = xd`. The left side belongs to `p`; primality and
`x ∉ p` give `d ∈ p`. Consequently
`p ≤ (b) ⊔ (x) • p`. Since `(x)` lies in the Jacobson radical and `p` is
finitely generated, Nakayama gives `p ≤ (b)`. The reverse containment follows
from `b ∈ p`.

For the dimension bound, regularity identifies the finite generator count of
`m` with the actual Krull dimension. Dimension at most two therefore splits
into dimension at most one, where all ideals are principal, or dimension two.
In the latter case a height-one prime differs from `m` because `m` has height
two. Finally, regular-local domainness makes every nonzero principal generator
a nonzerodivisor, yielding the displayed singleton bases.

This module proves neither regular-local factoriality in arbitrary dimension
nor a scheme-level Cartier or contraction theorem. It assumes no supplied UFD,
regular sequence, free or projective ideal, excellence, completeness, Henselian
condition, characteristic, or ground field. Its quotient map, ideal image, and
ideal inclusion are the canonical ones.
