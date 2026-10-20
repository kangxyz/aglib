# Finite cyclic permutations

`FinRotate` uses the actual `finRotate` permutation, its centralizer and its
exact order at nonzero levels. `CyclicEnumeration` constructs the equivalence
between a chosen transitive finite permutation and the literal finite rotation,
then proves order and divisibility consequences. The initial point, transitivity
condition and finite cardinality remain explicit. These interfaces support
`Aglib.Algebra.Ring.Pi.FiniteProjection` and finite-cover applications.
