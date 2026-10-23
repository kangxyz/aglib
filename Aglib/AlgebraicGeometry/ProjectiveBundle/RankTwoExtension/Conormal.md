# Actual quotient ideals and local conormal frames

Import `Aglib.AlgebraicGeometry.ProjectiveBundle.RankTwoExtension.Conormal`.
`Conormal.conormalMap` is the canonical map between the actual pulled-back
kernel ideals for a factorization `i = i' ≫ b` with the same source.
The implementation is the native `Scheme.Hom.conormalMap` in
`Aglib.AlgebraicGeometry.IdealSheaf.Modules.ConormalMap`;
`Conormal.affineConormalMap` specializes this single construction to spectra.
`affineIdealElement` and `affineIdealElement_map` expose the original spectral
kernel section and its canonical ideal-map naturality. `conormalElement`,
`affineConormalElement`, `conormalMap_unit_top` and `conormalMap_element`
retain those sections under actual pullback. `hom_ext_of_globalUnitFrame`
detects equality on the original global frame generator.
`Conormal.coordinateIdealIso` frames the actual ideal module of polynomial
evaluation at zero by its original regular coordinate, over every
commutative ring. `Conormal.coordinateConormalIso` uses the existing native
regular-kernel conormal frame and the same original coordinate class.
`Conormal.coordinateConormalIso_generator` normalizes that actual frame over
`Polynomial.C`: the original coordinate class maps to the unit section.
`Conormal.infinityIdealChartIso` and `quotientIdealChartIso` are the
canonical ideal pullback maps on the original cartesian squares.

`quotientIdeal_locallyRankOne` proves local rank one of the actual kernel
ideal of the constructed quotient section on the whole bundle. The proof
uses the original coordinate ideal near the section and the unit ideal off
it. `quotientConormalChartIso` gives frames of the actual pulled-back ideal
on the original base frames, with no replacement line module.

The exact ring calculation `coordinate_change_error` and its native
extension-conormal consequence `coordinate_change_cotangent` express
`x/(1+t*x) = x` modulo the square of the original ideal. The literal
principal-localization coordinate is retained in `overlapCoordinate_error`.
`Sections.chart_one_translation_overlap` identifies the original Proj
transition with this coordinate map. `Conormal.overlapConormalMaps_equal`
compares the two canonical conormal maps on that same principal overlap.

`quotientConormalIsoOfCompatibleFrames` glues the original local frames to
an isomorphism of the actual conormal with the unit module, under the explicit
premise `QuotientConormalFramesCompatible`. Deriving that native restriction
compatibility from the overlap comparison remains open. Local rank one and
the overlap ring identity alone do not discharge the global premise.
