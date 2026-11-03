# Original models localized at a target stalk

Import `Aglib.AlgebraicGeometry.Stalk.ModelLocalization`.
The namespace is `AlgebraicGeometry.Scheme`.

For a dominant map `p : Y -> X` between integral schemes and an original
point `x : X`, `isIntegral_pullback_fromSpecStalk` proves integrality of the
literal `pullback p (X.fromSpecStalk x)`. The existing proof is extracted
unchanged from `Morphisms.Finite.Birational.NormalLocus`; that consumer now
uses this single lower implementation.

`isDominant_pullback_fst_fromSpecStalk` proves dominance of its original
first projection by lifting the original generic point. Neither theorem
requires properness, finite type, Noetherianity or a dimension bound.

`normalStalks_pullback_fromSpecStalk` uses the original flat-preimmersion
stalk isomorphisms to transfer normality. It needs only the original normal
source, not integrality of either entire scheme or dominance of the map.
This is not normality ascent along an arbitrary flat morphism.

For `p y = x` and a closed original point `y`,
`exists_closed_point_pullback_fromSpecStalk` supplies a closed point of the
literal pullback with first projection `y` and second projection the actual
closed point of `Spec (X.stalk x)`. Closedness comes from the embedding of
the first projection. The original map of stalk arrows is the existing
`Hom.stalkMapIsoOfIsPullbackOfFlatOfPreimmersion`, not a newly chosen model.
No completion, rationality, surface, finite-residue or resolution input is used.
