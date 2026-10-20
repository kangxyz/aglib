# Laurent series convergent at all positive radii

`AllRadii.lean` defines `LaurentSeries.AllRadii.Converges` by weighted absolute
summability of an actual sequence `ℤ → F` at every positive real radius.
`Series F` is the corresponding submodule of coefficient sequences. Its support
is unrestricted in both directions. Bilateral convolution constructs its
commutative algebra over a complete normed field. Under the additional
ultrametric hypothesis, a strictly dominant coefficient argument proves it is
a domain. `Meromorphic F` is its actual fraction field.

The same file constructs translation by an actual unit, positive integer power
substitution, their extensions to fractions, and pullback between the actual
period-fixed intermediate fields under a supplied power relation. It proves
that the weighted summability condition is equivalent to coefficient decay at
every positive radius. The target field's complete norm and the specified
isometric scalar map are retained for convergent series evaluation.

`Evaluation.lean` defines `EvaluatesAt`, `regularAt`, and `evaluationAt`. A
fraction qualifies through a presentation whose actual denominator evaluates to
a nonzero value. The evaluation homomorphism has domain `regularAt f u`; there
is no evaluation homomorphism on the whole fraction field.
`EvaluationOperations.lean` supplies polynomial operations and inversion only
when the actual value is nonzero. `PowerEvaluation.lean` preserves qualifying
presentations under positive power substitution, checking the denominator at
the powered evaluation point.

These are generic analytic and field-algebra suppliers. No Tate parameter,
theta function, curve, uniformization, analytic algebraization, or identification
of the period-fixed field with a curve function field is constructed.
Source identities and original hypotheses are recorded in each leaf.
