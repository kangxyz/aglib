# Linear algebra

[Tensor-product maps](TensorProduct/README.md) give a commuting-square criterion for
transporting injectivity between specified tensor maps over a commutative ring.
The source and target comparisons are linear equivalences, the input tensor map
is assumed injective, and the tensor coefficient module is arbitrary. Import
the focused
`Aglib.LinearAlgebra.TensorProduct.Map` leaf for these comparisons.

[Multilinear maps](Multilinear/README.md) on spans: a multilinear map in finitely many
variables sends families of vectors of `span R T` into the span of its values on families of
vectors of `T`, over a commutative semiring. Import `Aglib.LinearAlgebra.Multilinear.Span`.

[Exterior powers](ExteriorPower/README.md) extend the native exterior objects
by semilinear maps and top-degree basis/determinant comparisons over arbitrary
commutative rings. [Dependent sums](DFinsupp/README.md) retain the native
subtype restriction and identify it as a linear equivalence when every omitted
fiber is subsingleton, over an arbitrary semiring.
