# Actual saturated affine atlases

`AffineAtlas.lean` supplies the exact original `BlowupAffineAtlas` family through
`Scheme.Blowup.blowupAffineAtlas`. Its original Noetherian premise is retained in
that family type. The direct construction `affineAtlas B` works for an arbitrary
commutative base ring and any given universal representative `B` of the original
quotient centre.

`affineProjAtlas I` uses exactly the existing `affineProjChart I a` for every
original `a : I`, with the original `affineChartMap` triangles and
`affineOverlapMap` localizations at the literal ratio `b/a`. Coverage and overlap
equalities are the previously proved native Rees Proj facts. The existing
`AffineAtlas.transport` transfers this atlas along the unique comparison with
`B`; chart rings and localization maps remain unchanged.

For local constructions, `spectrumIdeal J` transports the ideal of global
sections of an actual ideal sheaf `J` on `Spec A` through the canonical
`ΓSpecIso.hom`. `affineCenter_spectrumIdeal` proves that its original quotient
centre is exactly `J`, including its scheme structure. `spectrumDatum J` is the
original native Rees Proj datum for this ideal, with the original structural map.

These constructions use no supplied atlas or existence family. They feed the
independent properness proof and the actual global gluing construction. The
focused consumer is `AglibTest.BlowupGlobal`; source-bound compilation receipts
are recorded separately.
