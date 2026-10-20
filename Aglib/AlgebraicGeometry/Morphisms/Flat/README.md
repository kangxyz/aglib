# Flat germs, source descent and generic fibres

[AffineStalk](AffineStalk.lean) proves
`IsAffineOpen.flat_specMap_germ` for the actual affine germ using its canonical
localization. Canonical stalk-spectrum flatness is reused from
`Scheme.fromSpecStalk_flat` in `Stalk.FlatBaseChange`.

[DVRBaseChange](DVRBaseChange.lean) provides
`Spec.algebraMap_flat_surjective` from faithful flatness of the actual algebra.
In `Scheme.LocalRing.GenericFiber`, `baseMap_openImmersion` treats the specified
fraction field of a DVR. `dvr_isPullback` gives the literal ring/fraction-field
square for an injective local DVR map and a fraction-field homomorphism
satisfying the displayed scalar triangle. Ramified maps are allowed; no
ramification index is fixed.

[GenericFiberCriteria](GenericFiberCriteria.lean) keeps three separate results.
Over a Dedekind domain, an injective map into an algebra flat over the base
implies flatness of the source algebra. The corresponding pointwise flat-chart
and flat-surjective-source descent results are in `AlgebraicGeometry.Flat`.
They impose no source reducedness or quasi-compactness assumption.

For a flat locally finitely presented scheme over a domain, the actual
fraction-field projection is dominant. Reduced source together with integral
generic fibre then gives integral source. Reduced generic fibre gives reduced
source assuming flatness alone; local finite presentation is unnecessary for
that last result. These results use `Scheme.LocalRing.GenericFiber.baseMap`,
not a supplied replacement generic fibre. The common generic-point formula is
owned by `Stalk.GenericSection`.

The leaves preserve the exact maps and assumptions of the frozen R5 packet at
`f8a3314ddecffcada2ec721d26d56a937bed9690`. They supply general local geometry,
not a purity or flat-local regularity theorem.
