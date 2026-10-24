# A Kähler basis from generators and dual derivations

Let `R → A` be an algebra of commutative rings and let `g : ι → A` be a
finite family whose actual `Algebra.adjoin R (Set.range g)` is all of `A`.
Suppose actual derivations `δ i : Derivation R A A` satisfy
`δ i (g j) = if i = j then 1 else 0`.

`basisOfDerivations` constructs a basis of the ordinary algebraic Kähler
module with value `KaehlerDifferential.D R A (g i)` at `i`. Its coordinate
at `i` on `d a` is exactly `δ i a`; the basis and orientation are determined
by the original indexed generators and derivations.

The coordinate map consists of the universal Kähler lifts of the
derivations. Its inverse is the finite sum `∑ i, v i • d(g i)`. One inverse
identity follows from the displayed duality equations. For the other,
the induced derivation agrees with the universal derivation on every
generator, hence on their actual algebraic adjoin. The universal property
then gives equality on the entire differential module. No continuity,
smoothness, or freeness assumption on the differential module is used.

The intended consumer is the two- or three-generator differential basis of
the original `k[[u,v]]` over its specified expanded coefficient subring.
The finite series basis proves its algebraic-generation hypothesis; actual
coefficient and spatial derivations prove its duality equations. This leaf
does not assert those hypotheses for an arbitrary series scalar action.

The proof uses the algebraic derivation and Kähler universal properties
described above. Its foundation is Mathlib's algebraic derivation and Kähler
APIs at `d13f23b723b8a846827a245b89c10fc7d3f11612`, with Lean 4.34.1.
