# Postnikov triangles with the specified unit

This module starts from an actual map `u : M[0] → K`, with `K ≥ 0` and
invertible original `H⁰(u)`. Its canonical lift to `τ<1 K` is an isomorphism:
both objects are concentrated in degree zero, and the lift retains the
original equation `lift ≫ truncLTι = u`.

Transport of the native truncation triangle gives a distinguished triangle
whose literal first arrow is `u`. If `K ≤ 1`, the third object is the single
of the original `H¹(K)`, identified using the native homology-normalized
comparison and the original truncation projection. The connecting morphism
is retained; neither a splitting nor a vanishing of that morphism is claimed.

The last two declarations take the actual first-homology maps of a
distinguished triangle. Vanishing of `H⁰` of its third object and `H²` of
its first object makes this same short complex short exact. The geometric
consumer derives those vanishings from lower t-exactness and the actual
closed-fibre dimension theorem.

The source of the unit is not reconstructed from an abstract isomorphism of
cohomology groups. The geometric consumer uses the installed
`Functor.rightDerivedSingleUnit` from `BaseChange/ZeroComparison`.
