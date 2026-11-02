# The same rank-one torsion quotient

Source: [TorsionQuotient.lean](TorsionQuotient.lean).

`LinearMap.exists_linearEquiv_of_surjective_of_ker_le_torsion` retains two
actual maps `q : M →ₗ[B] L` and `v : M →ₗ[B] N` over a commutative domain.
Both are surjective, `ker q` lies in the native torsion submodule, `L` has
a supplied linear frame over `B`, and `N` is torsion-free and nontrivial.
It constructs an equivalence `e : L ≃ₗ[B] N` with the exact equation
`e.toLinearMap.comp q = v`. All four carrier universes are independent.

The factor is the native `Submodule.liftQ`, composed with the inverse of
`q.quotKerEquivOfSurjective`. Its value equation is proved before bijectivity.
After the supplied frame, native `LinearMap.ext_ring` identifies it with
`toSpanSingleton B N (g 1)`; native `LinearMap.ker_toSpanSingleton` supplies
injectivity. No second rank-one injectivity proof or quotient model is added.

Nontriviality is necessary: the zero quotient of a line is not a line.
The domain hypothesis is also genuine: torsion-freeness for regular scalars
over a general ring does not rule out a zero-divisor kernel. No local,
Noetherian, finite, finitely presented or target-rank assumption is used.

The intended geometric consumer supplies `q` from the SAME actual image
ideal, its torsion kernel from original pullback-stalk comparison, and `v`
from the original inverse-trace canonical pullback. Its surjectivity and
canonical target torsion-freeness/full support remain genuine geometric
obligations; this algebra theorem does not discharge them.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/LocalImageFrame](../../AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/LocalImageFrame.md).
