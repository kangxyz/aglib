# Derivations on actual fraction fields

`FractionRing.lean` extends a supplied `k`-derivation on a commutative domain `A`
to its actual fraction field `K`, retaining the explicit algebra structures and
scalar tower in independent universes. `Derivation.FractionRing.tangent` encodes
the derivation in the native `TrivSqZeroExt K K`; native localization lifts that
ring homomorphism. Its second coordinate is the derivation extension.

The original-ring equation, quotient rule, and uniqueness against any other
derivation with that same equation are proved. There is no analytic series,
Tate parameter, or theta-function dependency. The source is exactly the pure
fraction-derivation prefix of the frozen `Tate.Theta` container.
