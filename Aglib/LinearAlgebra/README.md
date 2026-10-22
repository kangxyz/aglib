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

[FreeModule](FreeModule/README.md) supplies rank-one stable cancellation
over arbitrary commutative rings and the actual ZMod torsion-module
interfaces; [Matrix](Matrix/README.md) supplies scalar restriction matrices and
determinants for the chosen basis. The latter is consumed by
[FGModuleCat/ScalarMatrices](../Algebra/Category/FGModuleCat/ScalarMatrices.lean),
with no separability hypothesis.

[KernelFiltration](KernelFiltration.lean) identifies the quotient of consecutive
ordinary transition kernels with the original adjacent kernel when the first
transition is surjective. The maps and quotient evaluation formula are retained;
no adic compatibility or finite-generation assumption is made.

[KernelFiltrationMap](KernelFiltrationMap.lean) retains a specified original composite in the canonical
map between reduction kernels and computes its kernel. The comparison
is surjective when the first map in the composite is surjective.

[DirectSum/Kernels](DirectSum/Kernels.lean) identifies the direct sum of original linear-map kernels
with the kernel of the original componentwise direct-sum map, retaining every
original inclusion.

[KernelIdealBound](KernelIdealBound.lean) transports an actual kernel containment in an ideal multiple
along an original commuting square of linear equivalences.

[LinearIndependent/FiniteBasisChange](LinearIndependent/FiniteBasisChange.lean)
transports independence of finite product families through a change of basis
of the same finite coefficient span. It retains the supplied field maps and
their scalar compatibility; the valued parameter-monomial argument uses this
to pass from an orthogonal basis to the original independent coefficients.

[DefectIdealBound](DefectIdealBound.lean) transports one ideal bound on both
the kernel and cokernel through a commuting square of the original linear
equivalences. [DefectRestriction](DefectRestriction.lean) restricts an
extended-ideal bound to the original scalar ring, with the stated scalar
towers. Neither result needs finiteness or flatness. The affine bounded
reconstruction in Grothendieck existence uses these bounds on its actual
comparison maps.
