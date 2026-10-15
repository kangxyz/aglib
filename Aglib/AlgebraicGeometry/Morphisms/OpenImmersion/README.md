# Open ranges in cartesian scheme squares

[Cartesian](Cartesian.lean), imported as `Aglib.AlgebraicGeometry.Morphisms.OpenImmersion.Cartesian`, gives `AlgebraicGeometry.Scheme.Hom.opensRange_of_isPullback`. In a supplied square `a,b,f,g`, with `a` and `g` open immersions and `IsPullback a b f g`, the actual open range of `a` is the inverse image under `f` of the open range of `g`.

This is a scheme/open-set equality. It assumes neither flatness of the arbitrary remaining map nor a sheaf, coherence or derived-category structure. The separate [module open-base-change comparison](../../Modules/BaseChange/OpenImmersion/README.md) and Godement local section diagrams consume this geometric identification.
