# Finite cyclic characters

`Characters` extends `AddMonoidHom.CyclicCharacters`: additive character order,
image exponent/cardinality, surjectivity at the specified `ZMod n` level,
rank-two kernel cardinality and unit coefficient markings. The nonzero-level,
cardinality, cyclicity and surjectivity hypotheses stay where required.

The module consumes generic equivariant quotient algebra and Mathlib's native
additive homomorphisms. Current consumers are primitive continuous characters,
pointed finite-etale coefficient covers and finite cyclotomic characters.
