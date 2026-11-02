# The same global canonical coefficient onto its actual local image

Source: [LocalImage.lean](LocalImage.lean).

The telescope is exactly that of `NormalSurface.LocalIdeal`: the original
integral normal surface embedded in the specified finite-coordinate
projective space over the regular local domain, its dimension bound and
finite generic-image base map, and an arbitrary original point `x`.
The new model is an arbitrary scheme `T` with an actual map
`beta : T → Spec (X.stalk x)`.

`normalSurfaceCanonicalLocalImageQuotient` has the literal source
`(beta ≫ X.fromSpecStalk x)^* W`, where `W` is the SAME original global
canonical module. The native pullback-composition isomorphism, pullback of
the accepted `normalSurfaceCanonicalLocalIdealIso`, and the existing
ideal-image epimorphism define its map. The target is the literal ideal
module of the SAME numerator's comap along `beta`, not a second image or
an assumed canonical module on `T`.

Its epimorphy and original inclusion equation hold without integrality,
dominance, flatness or Noetherianity of `T`. The inclusion equation is the
actual pullback of the accepted scaled canonical inclusion through the
native composition and unit maps. Consequently the existing original
denominator and generic-frame germ laws remain attached to this map.

For integral `T` and dominant `beta`,
`normalSurfaceCanonicalLocalImageQuotient_stalk_ker_eq_torsion` identifies
the kernel on every original stalk with the torsion of that literal global
coefficient pullback. It derives nonzeroness of the SAME numerator and
transports the accepted actual affine-image kernel through the native
source isomorphism, using the original module-stalk functor.

The existing `NormalizedPointDomination.Ideal` theorem can make this SAME
target locally rank one when the original stalk ring is genuinely normal,
Nagata and of dimension at most two. Those hypotheses do not follow merely
from this coefficient telescope and are not inserted here. No new canonical
object on an arbitrary local model, Gorenstein conclusion, regularity,
resolution, all-choice invariance or singular-path factorization is claimed.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/LocalImageFrame](LocalImageFrame.md).
