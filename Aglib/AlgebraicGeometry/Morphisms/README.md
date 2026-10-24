# Properties and local comparisons of scheme morphisms

This family uses the native Mathlib morphism properties. [Etale morphisms](Etale/README.md) give actual stalk comparisons and locally finitely presented etale-neighborhood detection. [Finite morphisms](Finite/README.md) give finite lift sets over arbitrary fields and lift algebraically closed field-valued points through finite surjective maps. [Closed immersions](ClosedImmersion/README.md) transport local/global Noetherianity from the target.

[Smooth morphisms](Smooth/README.md) provides polynomial charts and field-scheme reducedness, regularity, normality and dimension. Closed-point/nonempty hypotheses distinguish dimension equalities from the all-stalk upper bound. Actual module pushforward/pullback and their coherent/exact specializations remain in [Modules](../Modules/README.md).

[OpenImmersion](OpenImmersion/README.md) gives the exact opens-range equality for an actual cartesian square, below module and derived base-change comparisons.

[FiniteEtale](FiniteEtale/README.md) owns the full category of schemes over an
arbitrary base selected by finite etale structural morphisms, its fibres and
actual base-change functors. Field-valued fibre finiteness holds over arbitrary
fields; the geometric-point comparisons retain their separably closed field
hypotheses. Surjectivity is not an object condition.

[FormallyUnramified](FormallyUnramified/README.md) proves equality of lifts
through separated, formally unramified, locally finite-type maps when they
agree on a specified section of a geometrically connected family.
[Proper](Proper/README.md) constructs graph closures and, over Noetherian
affine bases, proper surjective modifications finite over finite projective
products. The separate cohomology family consumes these actual maps to prove
proper coherent finiteness.

[ImageComplement](UniversallyClosed/ImageComplement.lean) gives, for a universally closed
`f : X ⟶ Y` and a closed `C ⊆ X`, the open complement `f.complImage C` of `f(C)`: the points over
which `C` is empty, universal for base change (`Scheme.preimage_complImage_eq_top_iff_of_isPullback`;
Stacks 01JT). For `i : X ⟶ W` and an open `O ⊆ W` it is the open locus where the fibres of `f`
map into `O`, universal for "the base change maps into `O`"
(`Scheme.preimage_complImage_compl_preimage_eq_top_iff_of_isPullback`). No flatness or
Noetherian hypothesis is used.

[Integral generic lifts](Integral/GenericSection.md) extend a specified
generic lift through an integral morphism uniquely from a normal integral
scheme. The actual extension preserves both original structural and generic
triangles. No Noetherianity, dimension or reducedness condition is imposed on
the integral target; finite morphisms are included.

Focused guides for [finite flat morphisms](FiniteFlat/README.md),
[flat morphisms](Flat/README.md), [isomorphisms](IsIso/README.md) and
[surjectivity](Surjective/README.md) document the incoming affine/stalk and
generic-point comparisons. Rank, length and fibre-cardinality statements keep
their displayed finite-flat, local and coefficient hypotheses.

[SpreadingOut](SpreadingOut.md) constructs an actual smooth proper
geometrically integral curve family over a finitely generated integer
subalgebra of the original field, containing prescribed finite constants.
It also restores these properties on a literal later base change of a
given finitely presented qcqs model, with the original field comparison.
The [generic-open theorem](GeometricallyIntegral/Open.md) concerns proper
smooth relative curves over integral locally Noetherian bases and retains
geometric integrality of every original fibre on the resulting open.

[Separated/Cover](Separated/Cover.lean) proves that `f : P ⟶ S` is separated when opens `U i` cover
`P`, each `U i ⟶ S` is separated, and any two `U i` are disjoint or both contained in a third
(`isSeparated_of_cover_of_disjoint_or_le`; Kleiman, arXiv:math/0504020v1, proof of Thm 4.8, p. 28,
contains the disjoint and the increasing cases). Special cases:
`isSeparated_of_cover_of_pairwise_disjoint`, `isSeparated_of_cover_of_directed`, and the strata form
`isSeparated_of_cover_of_disjoint_of_monotone` (disjoint in one index, increasing in a directed
one). The proof checks that the range of the diagonal (an immersion) is closed, through the open
immersions `U k ×_S U k ⟶ P ×_S P` (`Scheme.Pullback.range_map`). No finiteness or Noetherian
hypothesis.
