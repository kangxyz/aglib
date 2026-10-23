# Dimension after adjoining an algebraic generator

Import `Aglib.RingTheory.KrullDimension.Monogenic`.

`IsAlgebraic.ringKrullDim_le_of_adjoin_singleton_eq_top` applies to a
Noetherian domain R and a commutative R-algebra S with an element b such
that `Algebra.adjoin R {b} = ⊤`. If b is algebraic over R, then

```text
ringKrullDim S ≤ ringKrullDim R.
```

The theorem uses the given algebra structure and its actual polynomial
evaluation map. The target need not be a domain, and the dimensions may
be infinite. Injectivity, finite generation as a module, normality,
locality, and catenarity are not additional premises.

Algebraicity supplies a nonzero p in R[X] with p(b) = 0. The generating
condition makes the evaluation R[X] -> S surjective. Since R is a domain,
p is a nonzerodivisor. The native theorem
`ringKrullDim_succ_le_of_surjective` gives

```text
ringKrullDim S + 1 ≤ ringKrullDim R[X].
```

The Noetherian polynomial formula
`Polynomial.ringKrullDim_of_isNoetherianRing` identifies the right side
with `ringKrullDim R + 1`. Addition of the finite element 1 is
order-cancellative in the extended dimension type `WithBot ℕ∞`, including
its infinite value, so the stated inequality follows.

The current consumer is the tower of actual generator subalgebras in a
generically finite surface-chart algebra. At each step the current
coefficient ring must be a Noetherian domain and the next generator must
be algebraic for that coefficient map. Once these facts are supplied,
the theorem preserves a dimension bound of two. It does not itself
construct the finite-generator tower, prove its algebraicity from an
actual extension of fraction fields, or prove Nagata stability. Those
remain separate inputs to the surface normalization argument.
