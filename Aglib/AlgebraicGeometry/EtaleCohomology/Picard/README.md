# Ordinary Picard classes in étale cohomology

[Pullback](Pullback.lean) specializes the existing `FrameTensor.picardH1Equiv` using the
proved étale line-bundle descent and `stacks03AJ` suppliers. Its source is the
original tensor/dual `Modules.Invertible.PicardGroup`; its target is original
`Sheaf.H (gm X) 1`, not a replacement cohomology carrier.

The geometric map in every degree is `gmCohomologyPullback`: original
`cohomologyPullback` followed by the adjoint of the existing `gmUnit`. This
coefficient morphism is not claimed to be invertible. The actual pullback of
ordinary frames gives `frameAdjointHom`, and
`picardCohomologyEquiv_pullback` identifies its degree-one map with the
existing `pullbackClass` on ordinary line bundles.

These results hold for arbitrary schemes and arbitrary morphisms in the same
scheme universe, with coefficients in the standard value universe `u + 1`.
Source and target `HasExt` universes are independent. No smoothness,
Noetherianity, properness, characteristic or curve hypotheses are imposed.

The `Kummer/Boundary` and `Kummer/BoundaryNaturality` leaves consume this
comparison. Their actual connecting homomorphism and pullback square require
only a positive integer invertible in the source's global sections. They do
not assert the boundary is surjective; the [broad-curve endpoints](../Curves/PrimeToCharacteristicVanishing.md)
supply separate geometric surjectivity and vanishing consumers.

[KummerQuotient](KummerQuotient.lean) uses native long-exact-sequence exactness to identify
`ker(picardBoundary)` with the range of multiplication by `n`. It constructs
`picardQuotientBoundary` on `QuotientAddGroup`, proves that map injective, and
proves its arbitrary-geometric-pullback square with the quotient of the native
Picard pullback. The quotient is of the original Picard group, not a second
Picard carrier or a redefined H2. Surjectivity is deliberately not asserted.

[LocalRing](LocalRing.lean) transfers the existing triviality of ordinary Picard groups on
local spectra through this same comparison. Thus original `H1(gm(Spec R))`
is a subsingleton for any local commutative ring, in particular for a field.
It introduces no replacement coefficient or cohomology group.
