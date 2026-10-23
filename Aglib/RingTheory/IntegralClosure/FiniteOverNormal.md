# Finite normalization over an integral model of a normal base

`integralClosure.equivOfIntegral R S A` compares the two literal integral
closures in the same ambient algebra `A` when `S` is integral over `R`.
The compatible maps `R → S → A` are part of the interface. The comparison
and its inverse send every element to itself in `A`. Transitivity of
integrality proves one direction, and extending the coefficients of a monic
equation proves the other. Neither normality nor finiteness is needed here.

For a normal Noetherian domain `R` with specified fraction field `K`,
`finite_base_of_integral_of_etale R K S A` proves that `integralClosure S A`
is finite over `R` when the actual generic algebra `A` is etale over `K`.
`finite_of_integral_of_etale` gives finiteness over the same model `S`.
The field version, `finite_of_integral_of_isSeparable R K S L`, assumes a
finite separable extension `L/K`. Normality of `S` is not required.

The field theorem uses Mathlib's existing `IsIntegralClosure.finite`, in
`Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`. That theorem places
the normalization inside the lattice spanned by the trace-dual basis of an
integral field basis. It uses normality of `R` to put integral traces in
`R`, separability for the nondegenerate trace pairing, and Noetherianity for
finite generation of the submodule. The finite etale version reuses the
existing `IntegralClosure/FiniteEtale.lean` product argument. There is one
implementation of each of these lower results.

This supplier applies to an actual integral model over a normal base with
the stated generic algebra. It does not apply to an arbitrary birational
blowup chart, which need not be integral over that base. It also does not
infer separability of a divisor's generic field from separability of the
surface projection. Both distinctions matter in the excellent-surface
resolution route. In characteristic two, the smooth curve
`y² + y = x³ + s*x` over `F₂(s)[[π]]` has separable degree-three y-projection
but its reduced y-zero divisor has the purely inseparable component
`x² = s`. The trace determinant for the basis `1,x,x²` is `(y²+y)²`, so this
phenomenon also occurs on the actual trace-discriminant divisor.
