# Homogeneous charts of actual quotients

Let `G` be a nonnegative grading on the original commutative algebra `D`,
let `f` have degree one, and let `J` be an actual homogeneous ideal.
`homogeneousQuotientEquiv` identifies

```
Away G f / map(dehomogenize, J) ≃ Away (G / J) (image f).
```

The proof applies the degree-one dehomogenizing quotient theorem on both
sides and commutes the ideals `J` and `(f - 1)`. It works with the literal
quotient grading. No flatness, domain or Noetherian condition is used.

`homogeneousQuotientEquiv_mk_dehomogenize` preserves every original
element after dehomogenization. The fraction formula sends the original
homogeneous fraction `x / f^n` to the fraction of its actual quotient
numerator with the same denominator and exponent.

The current consumer is the exceptional-chart comparison for the original
Rees algebra. This result does not identify a tangent cone with a polynomial
model or assert normality of an ordinary blowup.
