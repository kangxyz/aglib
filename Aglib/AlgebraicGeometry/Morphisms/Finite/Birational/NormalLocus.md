# Finite birational maps with normality off the isomorphism open

`Scheme.isIso_of_isFinite_of_isIso_restrict_of_normal_complement` proves
that a finite dominant morphism between integral schemes is an isomorphism
when it is an isomorphism over a nonempty open and its target stalks are
integrally closed at every point outside that open. It assumes neither
Noetherianity nor openness of the normal locus.

The proof forms the literal pullback to each required target stalk spectrum.
Its source is integral: the projection is a flat preimmersion with actual
stalk isomorphisms, and its embedded image contains the original generic
point. The local target spectrum has normal stalks by localization, so the
existing finite birational criterion applies there. The resulting local
isomorphisms, together with the original open isomorphism, prove bijectivity
and isomorphisms of the original stalk maps. Finiteness supplies the closed
map needed for the underlying homeomorphism.

The current consumer recognizes an actual point blowup on a scheme which
may be singular away from the centre. No excellence, J2, normalization
finiteness or normal-locus openness condition is imposed.
