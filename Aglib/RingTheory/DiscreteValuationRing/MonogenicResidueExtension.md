# A monogenic residue extension lifted to a DVR

Fix a DVR B, its actual residue field k, a field extension L/k, and a native
`PowerBasis k L` with generator α. The result constructs a particular monic
polynomial f over B lifting `minpoly k α`, and uses the literal ring

```text
D = AdjoinRoot f.
```

D is finite free over B. It is local, its maximal ideal is the extension
of the maximal ideal of B, and it is a DVR. The original uniformizer of B
remains a uniformizer in D. If B is complete for its maximal ideal, D is
complete for its own maximal ideal. L/k may be inseparable; perfectness is
not assumed.

The chosen power basis is genuine input specifying one monogenic residue
extension. The module does not claim that every finite field extension is
simple. Iterating such steps and constructing limit stages remain separate
obligations in the arbitrary-residue Cohen-ring construction.

The public construction is in the `PowerBasis` namespace:

- `residueLiftPolynomial` chooses a monic lift of the actual minimal polynomial;
- `ResidueLiftRing` is its actual root algebra;
- `residueLiftQuotientEquiv` identifies the literal quotient of D by the
  extended maximal ideal with L, as an algebra over B;
- `residueLiftPoint` composes the original quotient map with that equivalence.

The point sends the adjoined root to α and each coefficient a of B to the
image in L of its original residue. Its kernel is exactly the extended
maximal ideal. The map and all equations are constructed from the given
residue action, rather than from an unrelated isomorphic field.

Monicity gives finite freeness. The closed-fibre quotient is a field, so
the extended maximal ideal is maximal. Every maximal ideal of D contracts
to the maximal ideal of B by integrality, hence contains the extended
maximal ideal and equals it. This proves `residueLift_isLocalRing` and
`residueLift_maximalIdeal`. `residueLift_algebraMap_isLocalHom` supplies the
original local coefficient map.

Finite freeness and the nonzero field-valued point make the coefficient
map injective. A power of an original uniformizer therefore stays nonzero.
D is Noetherian because it is finite over B, and its actual maximal-ideal
topology is separated. The existing separated-principal-local-ring
supplier now proves `residueLift_isDomain` and
`residueLift_isDiscreteValuationRing`. No field-extension separability or
étale argument is used. The domain structure in the DVR conclusion is
the proved one.

`residueLiftResidueEquiv` is the resulting equivalence from the actual
residue field of D to L. Its value on `residue D x` is precisely
`residueLiftPoint x`. In particular it preserves the original coefficient
residue equation. `residueLift_isAdicComplete` applies finite-module
completeness and the proved equality of maximal ideals.

The source construction is the algebraic monogenic step of
[Stacks, Lemma 10.159.1 (03C3)](https://stacks.math.columbia.edu/tag/03C3),
specialized to a DVR and strengthened here with its actual DVR,
uniformizer, residue, and completeness conclusions. The root ring,
power-basis equivalence, finite freeness, and ideal maps are native
Mathlib constructions. This leaf supplies algebraic successor steps for
R.F2; it does not construct an arbitrary-residue Cohen ring or its map
into a given complete mixed-characteristic local domain.

Source basis: Aglib HEAD `8b93cc5940dc93f39a2eaf05e6985af28250a578`,
Lean 4.34.1, and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
