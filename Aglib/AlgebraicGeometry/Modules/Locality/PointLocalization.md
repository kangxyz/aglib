# Module epimorphisms at one point and away from it

Source: [PointLocalization.lean](PointLocalization.lean).

Import: `Aglib.AlgebraicGeometry.Modules.Locality.PointLocalization`.

For an original morphism `f : Y ⟶ X`, a closed point `x : X`, and an actual
Cartesian square over `X.fromSpecStalk x`, `epi_of_localization_and_away`
detects epimorphy of an arbitrary original module map on Y from its pullback
to that actual localization and to the inverse image of the complement of x.
It uses no properness, normality, coherence, finite type or Noetherianity.

The proof applies a private zero-object criterion to the original cokernel.
Over x the native Cartesian point-lift theorem supplies an actual point of
the supplied localization. Off x the original point lies in the literal
complementary-open subtype. The lower FlatStalk theorem detects the original
stalk zero in both cases. No global surjectivity of the localization, second
cover scheme or alternate module map is introduced.

This is a detection theorem, not a construction of canonical generation.
The intended canonical consumer must genuinely prove its local epimorphy
using curve generation and proper-local support, and its away epimorphy
using the actual blowup-away isomorphism and original trace base change.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/Trace/PointBlowupGeneration](../../Cohomology/Duality/Projective/Relative/NormalSurface/Trace/PointBlowupGeneration.md).
