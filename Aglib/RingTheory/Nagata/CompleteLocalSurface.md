# Complete local rings of dimension at most two

`IsJapaneseRing.of_complete_local_dimLE_two` gives the Japanese property
for a complete Noetherian local domain A of dimension at most two.
`IsNagataRing.of_complete_local_dimLE_two` gives the Nagata property for
a complete Noetherian local ring with the same dimension bound; this
second statement does not require A to be reduced or a domain.

The normalization interface
`integralClosure.finite_of_complete_local_dimLE_two A K L` retains a
supplied actual fraction field K, a finite extension field L, and the
original scalar tower A→K→L. Its conclusion is finiteness of the literal
`integralClosure A L` as an A-module. The extension may be inseparable.
All rings and tested fields lie in one ambient universe, with auxiliary
Japanese test universe zero, as in the existing finite-ascent interface.

For a domain of dimension two, the actual map constructed in
[FiniteRegularSubring](../LocalRing/FiniteRegularSubring.lean) makes A a
finite algebra over a complete regular local domain R0 of dimension two.
Regular-local normality applies to R0. The normal-surface Nagata theorem
and finite Nagata ascent therefore give Nagata, hence Japanese, for A.
The scalar action is the one induced by that constructed map. No
normality of A or finiteness of its normalization is assumed.

When the dimension is at most one, the existing complete-curve theorem
applies directly. These two cases prove the domain result without any
coefficient-field, perfect-residue, or separability hypothesis.

For the Nagata statement, every literal prime quotient A/p is a
Noetherian local domain of dimension at most two. Its completeness
follows from the finite-quotient completion theorem and the actual
surjective maximal-ideal equation. Applying the domain result to each
A/p supplies the defining Japanese condition. The quotient need not be
normal. The actual-fraction-field corollary then uses the existing
fraction-field comparison, preserving L and its original A-action.

The reduced normalization theorem
`integralClosure.finite_of_complete_local_reduced_dimLE_two R Q`
is CR2: the literal normalization of a complete reduced Noetherian
local ring of dimension at most two in its supplied total quotient
ring is finite. It applies the generic reduced-Nagata theorem in
[Normalization](Normalization.lean) to the Nagata predicate proved here.
That lower theorem uses the existing actual maps into the normalizations
of the minimal-prime quotients and their injectivity for a reduced base.
The original R-action on Q is retained, and Q may have its own universe.
The conclusion is module finiteness; no finite-length assertion is made
in dimension two.

The theorem,
`AdicCompletion.isReduced_of_finite_over_complete_local_dimLE_two`,
applies to an actual finite A-algebra B which is a local domain.
Finite Nagata ascent and integral dimension monotonicity allow
[Completion](Completion.lean) to prove that B's literal maximal-adic
completion is reduced. B need not be normal or complete, and A→B
need not be injective. This is a downstream use of reduced completion;
CN2 does not depend on it.

These statements do not assert arbitrary finite-type Nagata stability,
normality of completions, or resolution of singularities.
