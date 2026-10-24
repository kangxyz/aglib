# Nagata stability for surface coefficient rings

This module proves the dimension-two stability results needed by the general
surface-chart consumer. Every stability ring and tested extension field lies
in the same universe `Type u`; the Nagata and Japanese predicates retain
auxiliary universe zero.

`IsNagataRing.of_adjoin_singleton_eq_top_of_dimLE_two` treats an arbitrary
monogenic algebra over a Nagata ring of dimension at most two. The target may
have zero divisors and has no dimension premise. For each actual prime
quotient, its contracted coefficient quotient maps injectively to the target
quotient. A transcendental generator identifies that quotient with the
polynomial ring and uses polynomial Japanese stability. An algebraic generator
leads to normalization of the coefficient quotient in the original tested
finite field extension. That finite normal Nagata coefficient ring still has
dimension at most two. Rational adjunction B2 and identity-on-elements integral
coefficient comparison give finiteness of the original literal normalization.
`polynomial_of_dimLE_two` is the corresponding one-variable corollary.

`of_finiteType_isAlgebraic_and_dimLE_two` treats an injective finite-type map
into a domain whose target is algebraic over the coefficient ring. The
source domain property follows from injectivity into that domain and is
not a separate input. It returns
both the Nagata property and a proved dimension bound on the target. Its
finite-generator induction uses actual generated subalgebras. Each nonzero
algebraic relation remains nonzero over the intermediate coefficient domain;
the polynomial dimension inequality keeps every intermediate ring within
dimension two. The two projection theorems expose the Nagata conclusion and
the derived dimension bound separately.

Generic algebraicity can be supplied through compatible actual fraction
fields by `IsFractionRing.isAlgebraic_iff` and
`IsFractionRing.isAlgebraic_iff'`. The proof does not require separability.
`IsFractionRing.finite_of_finiteType_isAlgebraic` supplies the finite degree
of those fraction fields from finite actual algebra generators; it does
not require a separate domain assumption on the ring whose supplied
fraction ring is a field.

`of_essFiniteType_isAlgebraic_of_dimLE_two` extends the result to an
essentially finite-type algebraic domain with the original injective
coefficient map. The native essential-finiteness subalgebra is an internal
finite-type model; its actual localization is the original target ring.
`of_essFiniteType_isAlgebraic_of_complete_surface` supplies the coefficient
Nagata premise from completeness and dimension two of the original base.
It imposes no completion hypothesis on the target. The
[marked-path construction](../../AlgebraicGeometry/Blowup/Arc/MarkedPath.md)
uses these essentially finite-type interfaces for its actual tail stalks;
its original prefix residue-finiteness and marking inputs remain explicit.

The source corresponds to `nagata-stability-derivation.md`, SHA-256
`4a86145f7e3f4b377f01d8c3030d20b243be688e033969b84744a20e09084edc`,
using the polynomial-value rational-adjunction replacement, SHA-256
`5180910e263204d9db9a59b09857d9429cfa3b994d36b749dabf91b11db3cda9`.
The one-variable polynomial corollary is not iterated through arbitrary
polynomial rings of increasing dimension. These results do not assert
unrestricted finite-type Nagata stability or a surface resolution theorem.
