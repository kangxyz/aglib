# GenericPullback

Literal generic h1Pullback of SAME normalization Ext class, canonical coefficient/base-changed group comparison, and equality with SAME actual generic torsor class.

Source: `R5Lab.Aglib.AlgebraicGeometry.Normalization.GenericPullback`, R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.

Full source SHA-256: `b10035dc4da9fdf5ce6d802c64a6be28b8be7d191b581fe9631d8d022aaf2cce`.

Conditions: Retain independent HasExt universes w,wprime on Spec R and Spec K; all original GaloisCategory/FiberFunctor, Stacks03AJ/03RV on both bases, n>0, hkill, LevelInvertible, tau/coords/f/Q/hvan. genericFibreMap is already native GenericRestriction; comparison squares are actual maps, not a substituted H1 isomorphism.

Additional source: RestrictionInjectivity:368–399, SHA-256 `29621dcc998c54f85dd108228f23692084c687eec6e2a4411c3b711b06ddcdb9`.
genericInclusion, genericPoint_compat and genericFibreMap reuse native GenericRestriction.
FieldGaloisComparison:444–468 supplies the independent-action identity-coefficient
injectivity adapter here, after the actual genericCoefficientRestriction exists.

The source record is provenance. New native compiler coverage is reported separately; historical acceptance does not certify this extraction.

## Shared canonical forward maps

`pointedH1PullbackHom` is the literal `h1Pullback` followed by
`Naturality.pointedInverseImageH1AddEquiv`, as an additive map. Its group
homomorphism parameter is identified with the actual pointed group map by an
explicit equation. The generic specialization supplies the existing native
`GenericRestriction.genericFibreMap` and the reflexive equation; this adds no
premise to the normalization theorems and retains their original coefficient
action.

`pointedH1PullbackHom_apply` gives the original forward formula at the canonical
map. `genericH1PullbackComparison_eq_pointed` identifies the generic
specialization definitionally. Expanding these definitions and the reflexive
identification recovers exactly the former literal generic-pullback expression.
`normalizationExtClass_generic_comparison` and
`normalizationExtClass_generic_pullback` now share that same named forward map.
This is a presentation change, with no new cohomology carrier or replacement
normalization.

`genericH1PullbackComparison_injective` composes the existing normalization
coefficient pullback injection with the actual coefficient equivalence. Both
Ext universes, both Galois-category/fibre-functor inputs, the Stacks families,
and the original positive annihilator and invertibility conditions remain.
