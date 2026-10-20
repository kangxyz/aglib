# Units of positive integer level

`PositiveNat` proves `Algebra.isUnit_natCast_of_pos` for the actual ring map
from a characteristic-zero field into a commutative ring. The natural-number
level has its explicit `NeZero` instance. No local-ring hypothesis is required.

Additive notation for units is the canonical `Additive Rˣ`; the generic map is
`Units.mapAdditiveLinear` in `Aglib.Algebra.Group.Units.Map`. Historical
Milnor-unit aliases remain with their existing K-theory consumers.
