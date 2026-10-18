# Actual adjunction hom-equivalences

[MateHomEquiv](MateHomEquiv.lean), imported as `Aglib.CategoryTheory.Adjunction.MateHomEquiv`, gives `CategoryTheory.homEquiv_conjugate` and `homEquiv_to_identity`. They compare the actual adjunction hom-equivalences through a supplied natural transformation between left adjoints, retaining the original unit/counit maps. That transformation need not be invertible.

These generic categorical equations support scheme tensor/pushforward and projection-formula mates. They contain no scheme, flatness, finiteness or cohomology assumption; those belong to the geometric consumers of the comparison.

[Mates](Mates.lean) adds the actual four-adjunction comparison/unit identity and conjugate/mate whiskering transport, with independent category universes and explicit isomorphism conditions preserved.

[Unit](Unit.lean): `Adjunction.bijective_map_of_isIso_unit_app`: if the unit of `adj : F ⊣ G` is an
isomorphism at `N'`, then `F` is bijective on morphisms `N ⟶ N'`, for every `N` (the pointwise form
of Mathlib's `Adjunction.fullyFaithfulLOfIsIsoUnit`). Consumer:
`Picard/Comparison/LocallyTrivial.lean` (`q_T^*` on morphisms into trivial line bundles).

