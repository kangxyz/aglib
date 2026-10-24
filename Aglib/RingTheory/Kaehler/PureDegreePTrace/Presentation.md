# The actual monogenic differential presentation

Let `h : IsAdjoinRootMonic S (X ^ p - C a)` be the original presentation in a
scalar tower `Λ → R → S`. Write `P = KaehlerDifferential Λ R`.
Coefficient differentiation descends to a derivation on the actual algebra S
with values in `S ⊗[R] (P / R da)`. The kernel proof uses the literal principal
kernel of h, rather than a replacement quotient algebra.

The change between the two native polynomial-module carriers uses their
coefficient linear equivalences over Λ. Its application equation identifies
it with `PolynomialModule.map S` of the identity on the coefficient module,
so the evaluation and Leibniz formulas retain the original map.

Under `CharP R p`, `pureDegreePDifferentialDecomposition` gives

```text
KaehlerDifferential Λ S ≃ₗ[S] (S ⊗[R] (P / R da)) × S.
```

Its first component is the native universal lift of the descended coefficient
derivation. Its second is the original relative Kähler map followed by
`pureDegreePDifferentialEquiv`. The inverse sends a quotient base differential
to its original image and the scalar component to its multiple of `dz`.
Both inverse identities are proved; surjectivity uses the actual Kähler
transitivity sequence.

Neither freeness of P, nonzero da, a field hypothesis, nor finite p-rank is
assumed. Primality is unnecessary for this presentation supplier. Its current
consumer is `PureDegreePTrace.Exterior`.
