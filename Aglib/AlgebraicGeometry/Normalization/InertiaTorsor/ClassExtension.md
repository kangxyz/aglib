# ClassExtension

Define modelToGaloisH1 as literal generic h1Pullback/coefficient comparison/Galois restriction composite, show injective and exact image of normalizationExtClass, then unique model class for SAME A,tau,coords,f,Q.

Source: `R5Lab.Aglib.AlgebraicGeometry.Normalization.ClassExtensionUniqueness`, R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.

Full source SHA-256: `d946cc704625c81234aa7c88a505919dc11016f45e0cb07a92a85451bb48a25e`.

Conditions: Independent Ext universes wR,wK, exact source Stacks/descent/coefficient/level hypotheses remain. Reuse native generic_represented_h1Pullback_injective and surjective-map H1 restriction injectivity; do not duplicate connectedness or generic-fibre surjectivity proofs.


The source record is provenance. New native compiler coverage is reported separately; historical acceptance does not certify this extraction.

## Canonical composite correspondence

`modelToGaloisH1` is definitionally the original identity-coefficient Galois
restriction after `genericH1PullbackComparison`. Expanding that shared map and
`pointedH1PullbackHom` gives the original three-factor composite: literal
`h1Pullback`, its native inverse-image coefficient/field comparison, and the
original Galois restriction. The native generic fibre homomorphism and all
scalar actions are unchanged.

The injection proof uses `genericH1PullbackComparison_injective` and the same
surjective-Galois-map restriction injection. It does not repeat generic
connectedness, generic-fibre surjectivity or a lower normalization proof.
Existence and uniqueness still concern the same original algebra, torsor,
coordinates, point and chosen prime, under the source Ext/descent/level inputs.
