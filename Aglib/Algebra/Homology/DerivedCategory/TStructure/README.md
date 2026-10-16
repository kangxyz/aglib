# Native homology and concentrated derived objects

[Homology](Homology.lean) treats the original t-structure on the native
derived category of an abelian category with its specified
`HasDerivedCategory` structure. Object, morphism and derived-category
universes are independent. Enough injectives and a choice of complex
representative are not premises.

`homology_map_injective_of_isGE_of_isLE` detects equality of actual
morphisms between objects concentrated in the same degree.
`isoSingleHomology` identifies such an object with the native single of
its original homology in that degree. Its homology map, followed by the
original native single/homology comparison, is the identity.
`isoSingleHomology_hom_eq` makes this normalization unique, and
`isoSingleHomology_naturality` proves the original coefficient square.
The auxiliary single presentation does not change this normalized map.

Native Postnikov layers and geometric purity of a closed-immersion
right-derived object consume this single implementation. Bounded-below
specializations retain the original fully faithful inclusion; the lower
statement itself is not restricted to bounded-below objects.

[HomToSingle](HomToSingle.lean) handles an object with only an upper
cohomological bound n. `topHomologyProjection` is the native lower truncation
followed by its normalized homology single. `homToSingleAddEquiv` identifies
maps to a native single in degree n with maps from original Hn. Its forward
map, inverse projection and source/coefficient naturality retain the actual
arrows. No lower bound or injective/projective availability is required.
The homology of the original lower-truncation projection is also proved
invertible in each retained degree. Relative Serre degree-zero comparison
uses this lower interface.
