# Homothety on the same concentrated coinduced homology

For an original ring map `q : R → S`, coefficient module `N`, and native
injective resolution `I` of `N`, `coinducedCoefficientSingleIso` compares
the actual complex `q^!I` with the single of the original installed D+
coinduced homology. Its only concentration premise is vanishing of the
original ambient Ext groups away from degree `n`. The comparison is the
literal composite of `InjectiveResolution.rightDerivedFunctorPlusIso`
and the existing homology-normalized `Plus.isoSingleHomology`, viewed in
the selected derived category. No alternative canonical module is chosen.

`concentratedSelfHomologyExtLinearEquiv` transports the native module-valued
Hom cohomology to original self-Ext of that concentrated module. It uses
the original cocycle/localization comparison, the native fully faithful
shift functor, and native single/shift comparisons. The target Ext universe
is independent of both the carrier and selected derived category.

The degree-zero transport retains the actual scalar map.
`homothety_homologyMap_class` identifies its class with the original cocycle
of the scalar identity, using the existing single/cycle normalization.
`concentratedHomothetyEndLinearEquiv_apply` proves that the resulting map
into module endomorphisms is still `s ↦ s • id`, not merely some linear
equivalence between the same objects.

For a finite algebra over a regular local ring of specified finite
dimension, take `N = R`. The previously proved original homothety
quasi-isomorphism supplies all homothety assumptions internally.
`coinducedHomology_self_ext_subsingleton` gives vanishing of all positive
self-Ext of the same selected D+ homology.
`coinducedHomologyHomothetyLinearEquiv` gives its scalar homothety
equivalence, with the literal scalar formula recorded separately.

No locality of `S`, regular sequence presentation, projectivity or flatness
of `S` over `R`, canonical freeness, or resolution of singularities is a
premise. Ambient Ext, target Ext, and both derived-category sizes remain
independent. The later intrinsic Gorenstein implication must still prove
finite projective dimension of this module and the rank-one conclusion;
neither is asserted here.
