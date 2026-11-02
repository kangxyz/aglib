# The original affine centre at an actual stalk

Source: [Stalk.lean](Stalk.lean).

Import `Aglib.AlgebraicGeometry.Blowup.AffineCenter.Stalk`.

For an arbitrary commutative ring `A`, ideal `J` and actual point `p` of
`Spec A`, `affineCenter_stalkIdeal` identifies the literal stalk ideal with
`J.map (StructureSheaf.toStalk A p).hom`. It retains the original scalar
map, rather than choosing an isomorphic localization.

The two supporting laws `spectrumIdeal_affineCenter_eq` and
`spectrumIdeal_comap_fromSpecStalk_eq` identify the spectral ideal and its
extension to the original local spectrum. These three existing proof
bodies are owned here once. The original public names in
`Surfaces.Resolution.WeakTransform` and `Principalization` remain thin
same-statement wrappers.

There is no domain, Noetherianity, normality, regularity or dimension
hypothesis. No surface-resolution supplier is imported into this leaf.

Direct consumers: [AlgebraicGeometry/Blowup/AffineCenter/StalkKernel](StalkKernel.md), [AlgebraicGeometry/Surfaces/Resolution/WeakTransform](../../Surfaces/Resolution/WeakTransform.md).
