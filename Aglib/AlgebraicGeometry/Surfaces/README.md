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
records the remaining global canonical comparisons, rational/Gorenstein
reduction, geometric tangent-cone inputs, termination and descent obligations.
The chosen-embedding duality and ordinary rational-blowup results below are
prerequisites with their own hypotheses. In particular, the algebraic
[monic-quadratic theorem](../../RingTheory/GradedAlgebra/MonicQuadratic.md)
retains its actual relation and genuine Hilbert-function premises.

## Further completed prerequisites

The [birational guide](Birational/README.md#normalized-covers-and-finite-domination)
describes actual normalized ideal blowups and finite domination in an original
finite function-field extension. The
[cohomology guide](../Cohomology/README.md#surface-cohomology-with-original-coefficients)
records uniform scalar torsion, finite separable H1 transfer, a maximal model
from a supplied uniform bound, its complete-local R1 consequence, and
chosen-embedding GR with its actual regular-base map and closed embedding.
The [rational-blowup guide](RationalSingularities/README.md#ordinary-rational-blowups-and-the-full-exceptional-fibre)
retains the full exceptional fibre, positive ideal twists and original
power-section products under Nagata and universal H1-vanishing hypotheses.

## Normalized domination and prescribed local chains

[Normalized-point domination](Birational/NormalizedPointDomination.md)
constructs a finite normalized closed-point blowup chain dominating an
actual proper birational model over an integral normal Noetherian Nagata
surface. The target need not be regular. Its terminal is normal; regularity
is a separate conclusion when available.

[Completion descent](Resolution/CompletionDescent.md) descends an entire
supplied chain from the literal normal domain completion of a Noetherian
local surface, retaining its length and both terminal projection equations.
[Supported spreading](../Descent/LocalModification/SurfaceChain.md) extends
a supplied proper local chain at a closed nongeneric point of a normal
Noetherian surface, with the same length and the original stalk square,
and leaves its complement unchanged. Neither theorem constructs its
supplied local resolving chain.

[Rationality under completion](RationalSingularities/Completion.md) transfers
the universal original structure-H1 predicate to the literal normal domain
completion. It uses actual chain domination, prescribed descent and the
original flat cohomology comparison; arbitrary completed models are not
assumed to algebraize.

## Conditional resolving chains and remaining inputs

The [initial-cone endpoint](Resolution/RationalDoublePoint/NormalizedResolution.md)
constructs a regular terminal normalized-point chain with the original
regular-open isomorphisms. It retains universal rationality, genuine full
initial quadratic cones and an earlier complete-base map with finite
residue map. Later cones, marked tails and finite-chain termination are
constructed under those inputs. Deriving the initial cones from arbitrary
rational or rational-Gorenstein data remains separate.

The [cohomology family](../Cohomology/README.md) also contains coefficient-valued
curve Serre, correctly scoped Cartier restriction and finite canonical
comparisons. Generic differential, exterior, tensor, line and localization
constructions belong to their lower mathematical owners; the
[regular-pair one-pole family](../Blowup/Differentials/RegularPair/README.md)
and its point canonical comparisons consume those same constructors.
The global integral trace comparison, uniform all-model H1 bound and
unconditional rational/Gorenstein and RES/RES-QE constructions remain open.
A finite-Cohen-base wrapper is not applied to an arbitrary later stalk.
