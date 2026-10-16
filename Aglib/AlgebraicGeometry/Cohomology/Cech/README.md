# Scheme Cech exactness and comparison with Sheaf.H

[Augmentation](Augmentation.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.Cech.Augmentation`, constructs `Scheme.Cohomology.cechAugmentationZero` by restricting global presheaf sections to the degree-zero Cech intersections. For a scheme and open-family index in universe `u`, coefficients are any preadditive category with `HasProducts.{u}`. `cechAugmentationZero_π` gives the actual component formula and `cechAugmentationZero_d` shows that the signed first differential annihilates it. A zero object permits the cochain map `cechAugmentation` from the degree-zero single; `cechAugmentation_naturality` preserves the actual coefficient maps. No covering, affine or sheaf hypothesis is needed for these constructions.

[AffineDegreeOne](AffineDegreeOne.lean) and [AffineHigherExactness](AffineHigherExactness.lean) prove actual principal-cover Cech exactness for quasicoherent module coefficients on an affine scheme over any commutative ring. The cover is a finite principal cover; the numerator/denominator and higher exactness arguments preserve actual sections/restrictions. No Noetherian premise is added.

[InjectiveCoefficients](InjectiveCoefficients.lean) proves positive exactness for the original scheme Cech complex with injective module coefficients. [Restriction](Restriction.lean) gives actual Cech/restriction comparisons. Their lower section-representing open-free objects and generic [site Cech](../../../CategoryTheory/Sites/SheafCohomology/Cech/README.md) results are actual objects, rather than chosen replacement complexes.

[Comparison](Comparison.lean) uses the lower augmentation and [generic degree-zero criterion](../../../Algebra/Homology/CochainComplex/Augmentation.lean), identifies open `Sheaf.H'` with unchanged whole-space `Sheaf.H` in every degree and compares original Cech cohomology with it. The statement retains the actual cover/acyclicity hypotheses and proves coefficient naturality, H0 normalization and compatibility with structural scalars.

[FieldBaseChange](FieldBaseChange.lean) constructs `Scheme.Cohomology.structureCechComplex` and its canonical tensor/geometric comparisons for a finite family of affine opens in a separated field scheme. A covering premise is not needed for that complex-level comparison; its cohomology consequence uses the separate covering/comparison route. Generic finite coefficient comparison lives below schemes in [FiniteCoefficients](../../../CategoryTheory/Sites/SheafCohomology/Cech/FiniteCoefficients.lean).

Focused imports follow these leaves. [Canonical field base change](../BaseChange/README.md) consumes the precise scalar/naturality comparison with the original cohomology tensor map.

[Modules](Modules.lean) gives `moduleCechComplex`, using the shared
[`moduleSectionsPresheaf`](../Modules/Sections.lean),
for arbitrary module coefficients and any commutative structural ring
`α : R →+* Γ(X, ⊤)`. They use native scalar restriction of the actual module
presheaf. `moduleCechCohomologyLinearEquiv` computes original positive
`Sheaf.H` linearly over `R`, retaining a covering family, affine finite
intersections, quasicoherence and the supplied additive injective resolution.
`moduleAffineCechCohomologyLinearEquiv` supplies the affine-intersection
condition from separatedness and an affine open cover. No field, Noetherianity,
finite generation or properness is needed. The scalar-forgetting and homology
comparisons identify the original maps, rather than replacement cohomology.

[DegreeZero](DegreeZero.lean) identifies the actual Cech degree-zero homology
with global sections and with unchanged `Sheaf.H`, linearly over the same
specified structural ring. It uses the original restriction augmentation and
the sheaf gluing axiom. Only the covering premise is required; neither
quasicoherence nor affine intersections are needed in degree zero.
[DegreeZero/Forget](DegreeZero/Forget.lean) identifies its forward map with
the original augmentation and degree-zero section equivalence.
[DegreeZero/Geometric](DegreeZero/Geometric.lean) proves the corresponding
original geometric-map equation without a quasicoherence hypothesis.

[Modules/Naturality](Modules/Naturality.lean) constructs the original
`moduleCechMap` of a module coefficient morphism. Its scalar-forgetting,
homology and degree-zero augmentation comparisons preserve that exact chain
map. `moduleCechCohomologyLinearEquivAll_naturality` identifies its action on
homology in every degree with the original `Sheaf.H.map`, retaining the
specified structural ring, cover, affine intersections and positive-degree
quasicoherence/resolution premises. The degree-zero statement only needs the
cover. Projective twist multiplication consumes this interface directly.

[Geometric](Geometric.lean) proves the original Cech comparison is natural for
the actual `zariskiCohomologyMap` in every positive degree. It constructs an
exact-inverse-image resolution lift and identifies actual cycle/homology maps;
no comparison theorem is assumed. These generic proofs are shared with field
base change under their unchanged declaration names. The lower
[degree-zero comparison](../Functoriality/DegreeZero.lean) keeps this family
independent of the field-base-change implementation.

[Pushforward](Pushforward.lean) identifies the original geometric Cech map
for identity pushforward coefficients with the native pushforward-Cech
isomorphism. `moduleCohomologyPushforwardMap_bijective_zero` applies to any
morphism and module coefficient. Given actual target and preimage covers
with affine tuple intersections and quasicoherent coefficients on both
schemes, `moduleCohomologyPushforwardMap_bijective` proves bijectivity in
every degree. `moduleCohomologyPushforwardLinearEquiv` retains the specified
structural scalar action and has the original
`moduleCohomologyMapAlong f (𝟙 _)` as its literal forward map. The projective
closed-immersion comparison consumes these exact maps.
