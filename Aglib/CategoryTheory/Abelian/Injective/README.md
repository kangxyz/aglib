# Supplied resolutions and exact-functor Ext comparison

[ResolutionKernels](ResolutionKernels.lean), imported as `Aglib.CategoryTheory.Abelian.Injective.ResolutionKernels`, defines `CategoryTheory.InjectiveResolution.initialSequence` and `kernelSequence`. For a supplied actual injective resolution in an arbitrary abelian category, `initialSequence_shortExact` and `kernelSequence_shortExact` prove the actual augmentation/successive-kernel sequences short exact. This is not an existence theorem for resolutions in arbitrary categories.

[ExactFunctor](ExactFunctor.lean) uses `CategoryTheory.InjectiveResolution.ExactFunctor`. It constructs compatible lifts from the image of a resolution under an exact additive functor to an actual target resolution. `extMk_mapExactFunctor_comp_mk₀` identifies the original exact-functor Ext map, followed by the coefficient map, with the actual mapped cycle. Injectivity is used in the target resolution; preservation of source injectives is not assumed.

Source and target object, morphism and Ext universes are independent. The stated `HasExt`, derived-category availability, lift compatibility and normalization hypotheses remain explicit. The consumers are flasque/module-resolution dimension shifting and canonical scheme Cech/geometric comparison. [Total complexes](../../../Algebra/Homology/TotalComplex/README.md) supplies the complementary bicomplex interface.

[MapAugmentation](MapAugmentation.lean) supplies the original natural-degree
mapped augmentation `I.mapAugmentation F`, with literal component
`F.map (I.ι.f 0)`, the native single-comparison equation, and naturality for
each supplied original resolution lift. Preservation of finite limits
proves `mapAugmentation_quasiIsoAt_zero` for every coefficient. If the
original `F.rightDerived (n + 1)` vanishes on the chosen coefficient for
every natural `n`, the same augmentation is a quasi-isomorphism, as is
the literal `F.mapHomologicalComplex` image of `I.ι'`. The integer result
uses the sole native extension comparison and introduces no second
integer augmentation. No derived category, preservation of injectives,
or exactness of `F` on all objects is assumed. The source passed with
receipt `1792118239807175000-85090` in 2.1 seconds. The independent
four-universe `MapAugmentationConsumer.lean` passed with receipt
`1792118292786312000-86062`; the inspected declarations use only the three
standard axioms. Affine resolution sections and the installed
right-derived acyclic-single comparison consume this lower interface.
