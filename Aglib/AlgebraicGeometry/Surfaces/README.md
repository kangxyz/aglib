# Algebraic surfaces

This family develops scheme-theoretic results in dimension at most two.
The proper-base projectivity and contraction interfaces apply to general
Noetherian schemes with their stated regularity and properness hypotheses.
They do not require a chosen ground field, trait, or arithmetic presentation.
The trait and explicit-equation families below supply more specialized tools.

## Main interfaces

| Family | Interface and scope |
| --- | --- |
| [Projectivity](Projectivity.md) | A finite closed projective embedding of an integral regular Noetherian scheme of dimension at most two, over its original proper map to a Noetherian affine base. |
| [Contraction](Contraction/README.md) | Contraction of an original exceptional Cartier projective line in one fibre of a supplied proper map, with its field, ideal, blowup and complement comparisons. |
| [Birational geometry](Birational/README.md) | Graphs, regular-source common domination, Chow domination, exceptional-conormal comparisons and original-map factorization. Each theorem retains its own source hypotheses. |
| [Regular-source principalization](Resolution/README.md) | Finite closed-point blowups principalizing an actual nonzero ideal with Artinian quotient on an already regular integral surface. |
| [Normal graphs and punctured cohomology](Resolution/ExtensionGraph/Construction.md) | The literal finite normal graph and injectivity of original punctured structure-H1 restriction over a normal Noetherian Nagata local domain of dimension two. |
| [Regular-local universal vanishing](RationalSingularities/README.md) | Structure-H1 vanishing on every supplied normal proper birational model over a regular local ring of dimension two. |
| [Resolution necessity](Resolution/Necessity.md) | Finite generic normalization, a finite singular set and normal domain completions, derived from a supplied proper birational regular integral model. |
| [Power-node models](PowerNode/README.md) | Explicit affine, blowup and Cartier-divisor calculations for the stated power-node equations and coefficient rings. |

## Projectivity over the original affine base

`Scheme.Surfaces.exists_projective_embedding_of_isProper` starts with an
integral Noetherian scheme X, regular stalks, `topologicalKrullDim X ≤ 2`,
a Noetherian commutative ring A, and the actual proper morphism q:X→Spec A.
It constructs a finite index type J and a closed immersion p:X→P_A(J)
whose composite with the projective structural map is exactly q.
`exists_standard_projective_embedding_of_isProper` gives positive finite
standard coordinates.

The construction uses a projective Chow modification, a finite regular
point-blowup chain dominating it, and the closed comparison graph into the
literal pullback. Reverse contraction transfers the embedding back to the
original X. The supplied proper map is preserved throughout; projectivity
or an ample bundle is not an additional input. A surface without a supplied
proper map lies outside this theorem's scope.

## Contraction with the full point and Cartier ideal

[The proper contraction interface](Contraction/Proper.md), in
`Scheme.Surfaces.Contraction.Proper`, starts with an integral regular
Noetherian X of dimension at most two and a proper map f:X→S to a
Noetherian scheme. Its original closed immersion i:P¹_k→X has an actual
locally rank-one kernel ideal, conormal comparison i*ideal(i)≅O(1), and
singleton image in S. The field k is retained; it is not identified with
the residue field of that image point.

`exists_cartier_contraction_of_isProper` constructs an integral regular
Noetherian Y of dimension two, a proper surjective birational map b:X→Y,
a closed full-k point c:Spec k→Y, and a proper separated structural map
s:Y→S. The outputs include the original triangle b≫s=f, the exceptional
triangle for i, the literal equality `c.ker.comap b = i.ker`, the Cartier
pullback, the isomorphism of the canonical lift to the blowup of c.ker,
and the original complement isomorphisms. Birationality of f descends to s.
Separation is over S; absolute separation follows when S is separated.

The actual inverse image of an affine neighbourhood in S gets its finite
projective embedding from the projectivity theorem above. The projective
contraction is then glued with the original complement. The lower
[projective interface](Contraction/Projective.md) and
[explicit local-embedding interface](Contraction/Proper.md) remain useful
when that presentation is already supplied.

## Resolution tools and their hypotheses

`Scheme.Blowup.exists_regular_pointBlowup_principalization_of_dimension_le_two`
principalizes an actual ideal with Artinian quotient by a finite
`PointBlowupChain`. Its original source is already integral and regular.
The resulting composite retains properness, birationality, regularity and
the dimension bound. The weak-transform and colength arguments concern
the original embedded ideals and original stalks.

Regular-source principalization feeds
[common domination](Birational/CommonDomination.md) and
[Chow domination](Birational/ChowDomination.md). The trait interfaces keep
the original fraction field, literal generic fibres and section maps; their
additional trait hypotheses stay at those interfaces.

Resolution of an initially singular general surface remains a separate
construction. The regular-source chains above do not supply that theorem.
The ongoing general resolution argument requires its own finite
normalization, cohomological bounds, singular-centre iteration and descent.
Reusable local algebra, cohomology, blowup and descent results keep their
respective owners elsewhere in Aglib; this directory supplies their surface
consumers. No field, trait or projective-model restriction should be silently
substituted for a general surface hypothesis.

The [normal-graph construction](Resolution/ExtensionGraph/Construction.md)
and [regular-local universal vanishing](RationalSingularities/Regular.md)
retain their actual normality, properness, birationality and local-base
hypotheses. [Necessity](Resolution/Necessity.md) starts from a supplied
regular proper birational model and derives conditions on the original
normalization; it does not supply that model.

The complete resolution criterion RES and its quasi-excellent consequence
RES-QE remain open. The
[resolution guide](Resolution/README.md#open-resolution-construction)
records the remaining geometric duality, rational/Gorenstein, tangent-cone,
termination and descent obligations. In particular, the algebraic
[monic-quadratic theorem](../../RingTheory/GradedAlgebra/MonicQuadratic.md)
retains its actual relation and genuine Hilbert-function premises.
