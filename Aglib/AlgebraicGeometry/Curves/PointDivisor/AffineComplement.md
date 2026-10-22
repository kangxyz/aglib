# The actual complement of a pole

On an integral smooth proper curve of relative dimension1 over any field,
this lower pair constructs a finite projective-line map from an original
rational function that is regular away from a supplied closed point and has
a strictly negative order there. The exact inverse image of its affine chart
is the original complement, which is therefore affine.

The actual closed-stalk valuation is trivial on the original scalar field.
Its value is the exponential of the negative original order. A strictly
negative order proves transcendence by the native valuation theorem, in
every characteristic. The original rational function gives a literal
generic morphism to polynomial P1. Native normal-curve extension and
proper-dominant-curve finiteness retain the original scalar and generic
triangles. No desired map family or assumed presentation is used.

`RegularAway` means that an actual section on the original complement has
the specified original generic value. Its local map agrees with the finite
extension by generic uniqueness. If the pole itself were in the affine
chart, the actual chart coordinate would pull back to a regular section
near that point with the same generic value, contradicting its negative
order. These two directions prove the exact inverse-image equality.
The fixed polynomial-to-native-P1 isomorphism then transports the same map,
chart, scalar equation and generic equation to lifted native coordinates.

The public `openSectionValue` is the actual generic-germ algebra map with
the original field constants. Its injectivity and nonnegative-order theorem,
the `openToSpecΓ_constants` structural triangle, and
`genericValue_of_specMap_eq` for an arbitrary affine target retain the
actual maps needed by the upper Weierstrass construction.

The input closed point is supplied by the caller; it is not reselected here.
For the genus-one consumer it is exactly `PointDivisor.closedPoint X p hp`
from the separately owned PoleFunctions pair. This lower construction has
no dependency on that pair and no cycle with Presentation.

Basis: Original Aglib HEAD
`3a4d549981ced306d89d3ed55418c9e6a25f86c4` with the live overlay.
The complete source
`40ab04bb03da11ac83ef90aa3bbe443da429065660061d24aa172d2f4626626f`
passed natively in 7.3 seconds in
`remote-67d3408ff2c04d3da9baab748cb1fd8e`, SOURCE
`26c8017fcad513fedd7b5b48de4bc16e8cfb38158428f58edaf332cd9d73399f`.
This covers the exact complement, affineness and the lifted-native-P1 map
with its original scalar and generic triangles. Independent mathematical
review is separate; evidence for Maps or Sections is not substituted here.
