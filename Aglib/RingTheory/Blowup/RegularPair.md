# A regular pair and its saturated blowup chart

`Localization.Away.pairChartEquiv a b ha hb` compares the actual quotient
`A[X] / (a X - b)` with the actual subalgebra
`Localization.Away.saturatedChart A (Ideal.span {a, b}) a` of `A[1/a]`.
Here `ha` asserts that `a` acts injectively on `A`, and `hb` asserts that `b`
acts injectively on `A / (a)`. The result does not require Noetherianity,
locality, a domain, a field, or completeness as an extra premise.

The crucial cancellation is proved before the equivalence is constructed.
If `a p = (a X - b) g`, reduction modulo `a` and regularity of `b` imply
that every coefficient of `g` is divisible by `a`. Cancelling `a` in the
original polynomial ring proves divisibility of `p` by the original
relation. Consequently `a` remains regular in the quotient. The canonical
evaluation at `b/a` lifts to a map from `A[1/a]` to the localization
of the polynomial quotient at `a`. Its composite with evaluation is the
canonical localization map of that quotient, whose injectivity follows from
the proved regularity of `a`. The evaluation image is the subalgebra generated
by the fractions `c/a` with `c` in the original two-generated ideal.

The public coordinate and scalar equations retain the literal fraction
`b/a` and original algebra maps. They are intended to be consumed by the
actual affine atlas of the native Rees blowup.

`pairFibreEquiv` identifies the literal coefficient-ideal quotient of the
polynomial model with `(A / (a,b))[X]`; its variable remains the original
quotient coordinate. `pairChartFibreEquiv` transfers this through the proved
injection to the fibre ring of the actual saturated chart. The intermediate
polynomial-model fibre computation itself needs no regularity assumption.

`IsRegularLocalRing.exists_regularPair` supplies both orientations for the
actual maximal ideal of a two-dimensional regular local ring. A first
parameter has a one-dimensional regular quotient; lifting a generator of its
maximal ideal supplies the second parameter and the original two-generator
equation. Domainhood is derived from regularity. The same cancellation
argument proves that multiplication by `a` on `A / (b)` is injective,
giving regularity of the pair in the reverse order.

This algebraic chart comparison alone does not identify the global exceptional
divisor or its normal line. The geometric target is the exceptional-fibre and
normal-line calculation of [Stacks, Lemma 54.3.1, tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ).
The following [Lemma 54.3.2, tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
uses that calculation to prove regularity of the blowup. Those geometric
conclusions require their own actual scheme and module comparisons.
