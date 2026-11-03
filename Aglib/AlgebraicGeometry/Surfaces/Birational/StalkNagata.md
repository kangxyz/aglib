# Nagata stalks of actual birational surface models

Source: [StalkNagata.lean](StalkNagata.lean).

Import `Aglib.AlgebraicGeometry.Surfaces.Birational.StalkNagata`.
The native namespace is `AlgebraicGeometry.Scheme`.

`stalk_isNagataRing_of_birational_surface` takes a Nagata domain `A` of
dimension at most two, an integral scheme `X`, an actual locally finite-type
dominant map `f : X -> Spec A`, and invertibility of its ORIGINAL
function-field map. Every actual `X.stalk x` is Nagata.

The proof chooses an actual affine neighborhood, uses the original adapted
birational chart and localizes at the point's native prime. Its base top
chart is supplied by `affineCharts_isNagata_of_nagata`; the native GammaSpec
comparison is not duplicated. The original stalk algebra and prime-complement
localization remain unchanged.

This is the single stalk-localization body moved from
`Resolution/RationalDoublePoint/BlowupChildren`. The old public
`RationalSingularities.stalk_isNagataRing_of_birational_surface` keeps its
complete signature as a thin wrapper. Properness, normality, locality,
rationality, completeness and finite selected-stalk modules are not premises.

Direct consumers: [AlgebraicGeometry/Surfaces/RationalSingularities/ModelLocalization](../RationalSingularities/ModelLocalization.md), [AlgebraicGeometry/Surfaces/Resolution/RationalDoublePoint/BlowupChildren](../Resolution/RationalDoublePoint/BlowupChildren.md).
