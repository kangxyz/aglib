# Finite projective modules with two commuting automorphisms

`Module.CommutingAutomorphisms.Object R` bundles an actual finite projective
module and an ordered pair of commuting linear automorphisms. `Basic` supplies
intertwining isomorphisms, direct sums, unit pairs and coordinate exchange;
`BaseChange` supplies tensor extension and its identity/composition comparisons.

`LaurentSupport` constructs the action of
`MonoidAlgebra R (Multiplicative (ℤ × ℤ))`. The first and second exponents act
through the first and second operators, respectively. Its support is the actual
action-kernel quotient. That algebra is finite when `R` is Noetherian; the
represented module is finite and flat, while flatness of the support algebra
is not asserted. `SupportNaturality` constructs coefficient and support maps.
`FlatSupport` proves the support-ideal and support-algebra base-change identities
under actual coefficient flatness.

`Realization` tags the original carrier with its actual Laurent module action,
and proves its isomorphism, sum and annihilator comparisons. `SupportDominance`
and `LocalMultiplicity` derive dominant finite components and finite intrinsic
local lengths under their displayed domain, Noetherian and minimal-prime
hypotheses. `LocalLength` identifies intrinsic and ambient local lengths.

`SupportPoints` consumes the shared lower carrier
`MonoidAlgebra.FiniteDominantPrime` from
`Aglib.RingTheory.MonoidAlgebra.FiniteDominantPrimes`. Nonzero coefficients occur
only among actual minimal support primes. Natural coefficients are `ENat.toNat`
of actual lengths; the separate Noetherian finiteness theorem justifies their
cast back to `ENat`. `RealizationBaseChange` and `FlatMultiplicity` retain actual
flatness, Noetherian and domain conditions in their multiplicity formulas.

`PrincipalRegularity` proves scalar injectivity from regularity in the base
ring. `PrincipalSpecialization` identifies actual local scalar cokernels with
the scalar-extended target module for a surjective structural algebra map with
the stated principal kernel. That comparison requires no flatness and preserves
the full extended-natural length, including infinity. Regularity separately
supplies the Euler formula. `PrincipalEuler`, `PrincipalAssociativity` and
`PrincipalMultiplicity` use the existing scalar-homology and prime-filtration
theory; finite-length interpretations retain their explicit finiteness
conditions. The fully generic prime-quotient factor comparison is lower, in
`Aglib.RingTheory.Localization.PrincipalQuotientLength`, namespace `Module`.

The corresponding frozen R5 source identity is
`f8a3314ddecffcada2ec721d26d56a937bed9690`; individual leaves record exact paths
and SHA-256 hashes. Algebraic-simplex specializations and scheme-cycle adapters
are downstream consumers.
