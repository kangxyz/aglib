# Regularity at closed points and on a closed fibre

`Scheme.isRegularLocalRing_stalk_of_specializes` transports regularity from
an actual stalk to every generization. Its proof uses the original local
spectrum map, its actual stalk isomorphism, and regularity of prime
localizations of the given regular local ring.

`Scheme.regularStalks_of_regular_closedPoints` then checks `RegularStalks X`
at closed points when `X` is quasi-compact. A closed specialization exists
inside each point closure by compactness and the scheme's T0 property.
Global Noetherianity and openness of the regular locus are unnecessary.

For an actual proper map `f : X ⟶ Spec R` over a commutative local ring,
`Scheme.image_closedPoint_eq_closedPoint` places every closed source point
on the literal closed fibre. Properness makes its image closed, and the
local spectrum has a unique closed point. The resulting
`Scheme.regularStalks_of_regular_closedFibre` requires regularity of the
actual ambient stalks over that point and proves regularity everywhere.

The current consumer is the regularity step of surface contraction. The
Cartier regular-quotient argument must still supply regularity of those
ambient stalks; regularity of the fibre's own stalks alone is not the
hypothesis of the final theorem.
