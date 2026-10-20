# Norm factorization by polynomial roots

`RootFactorization.lean` works with the actual determinant norm and actual
simple field extensions. The product of norms of `1 - root`, over the normalized
irreducible factors of `X^q - a`, is `1 - a`. A selected family of roots in an
algebraically closed extension produces separable finite simple extensions when
`q > 0`, `a ≠ 0`, and `(q : K) ≠ 0`; the final existence theorem also retains
`a ≠ 1`. No characteristic-zero or perfection hypothesis is added.

The monic quotient-algebra norm calculation reuses
[`AdjoinRoot.norm_one_sub_root`](../../RingTheory/AdjoinRootNormEvaluation.lean).
No Steinberg relation or cohomological projection formula is assumed or proved.
