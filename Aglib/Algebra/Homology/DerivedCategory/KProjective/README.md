# Original maps from K-projective complexes

[Representatives](Representatives.lean) extends Mathlib's actual
`CochainComplex.IsKProjective` interface. For an abelian category with the stated
`HasDerivedCategory` choice, an original derived arrow with K-projective source
has an actual chain representative with the prescribed image under
`DerivedCategory.Q`. Equality of two such images gives an actual chain homotopy.
The object, morphism and derived-category universes remain independent.

[Comparison](Comparison.lean) lifts a chain map from a K-projective source
through an original quasi-isomorphism, with a genuine comparison homotopy.
It cancels a postcomposed quasi-isomorphism at the level of homotopies and
constructs a chain homotopy equivalence between two K-projective resolutions
of the same complex. These statements require neither term bounds nor enough
projectives. A standard derived-category choice is used locally inside the
comparison proofs, without installing a global instance or changing the maps.

[Bounded projective models](../../CochainComplex/BoundedAbove/README.md) consume
these comparisons after proving K-projectivity from an actual upper bound and
degreewise projectivity.
