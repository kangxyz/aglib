# Original unit-coefficient curve Serre duality

This adapter uses the actual chosen-embedding object and canonical module
from [`CohenMacaulayCurve`](../CohenMacaulayCurve.md). Its explicit `hCM`
hypothesis says that every closed stalk has a regular element whose
principal ideal has maximal radical. The source may be nonreduced over
an arbitrary field. No smoothness, normality, separability, integrality
or Gorenstein hypothesis is added.

The canonical homology degree is the integer `(n : ℤ) - 1`. The genuine
index premise `1 ≤ n` makes the original natural Serre index
`q = r + (n - 1)` valid. This adapter retains that premise; it does not
truncate an integer or assume a general finite resolution.

`cmCurveSerreDerivedLinearMap` is the literal original closed-embedding
Serre map, transported through the proved canonical reconstruction and
both installed single/shift comparisons. `cmCurveSerreDerivedDuality`
packages coherent-source bijectivity of that same map. The source
condition is the existing `affineLocallyFiniteType C F` condition.
The derived composition and source-morphism formulas retain native Ext,
original derived pushforward, and its installed shift signs.

For `r = 0, 1`, `cmCurveSerreDuality` has the actual target
`Hom_k(H^(1-r)(C,F), k)`. Its forward map is exactly
`cmCurveSerreCohomologyAddEquiv`: the original affine derived-Hom
comparison, native homology extraction, and original supplied-resolution
comparison with `Sheaf.H`. The scalar actions are the original structural
field action and the native Ext action. No perfect-pairing hypothesis,
new cohomology comparison, or independent choice of a duality map occurs.

The identity `cmCurveSerreCohomologyAddEquiv_pairing` identifies this
original functional on each original Ext/cohomology class with positive
Yoneda composition followed by the same existing `cmCurveSerreTrace`.
The proof transports the actual affine Hom comparison to original
module-valued derived sections, cancels its original derived single
unit, computes homology of the native single shift on its actual middle
component, and uses the original degree-one Ext action on the structural
section one. It introduces no compatibility equation as a premise.
This identity proves linearity and the full source/Yoneda naturality of
`cmCurveSerreDuality`.

`cmCurveSerreTrace` is the actual linear map on `H¹` of the canonical
module obtained from the same original degree-one Serre map, the actual
structural derived unit, and evaluation at `1` through the original
spectrum/global-sections isomorphism. `cmCurveSerreDuality_one` proves
that evaluation of the degree-one functional on the original structural
section one is this same trace. The native `UnitTrace` unit law supplies
the normalization; no field trace or coefficient orientation is chosen.

`cmCurveSerreStructuralH0Map` is the genuine structural
`k → H⁰(O_C)` map: its original section formula is the actual structural
ring homomorphism on every scalar. Under bijectivity of this displayed
map, `cmCurveSerreTrace_bijective` and `cmCurveSerreTraceEquiv` package
bijectivity of the same trace. A hypothetical perfect pairing or an
arbitrary identification of lines is not used.

The intrinsic surface coefficient line, the coefficient-valued curve family,
and the surface-to-curve Cartier comparison retain their separate
mathematical boundaries.

The family is split at actual intermediate consumers:
[`Derived`](Serre/Derived.md) constructs the original derived and additive
comparisons; [`Pairing`](Serre/Pairing.md) retains the positive Yoneda pairing;
[`Transport`](Serre/Transport.md) proves native single, localization and affine
module transports; [`Trace`](Serre/Trace.md) retains original structural-one
and UnitTrace normalizations; and [`Comparison`](Serre/Comparison.md) identifies
the unchanged additive comparison with that same positive pairing. This parent
module exports the final linear equivalence, naturality and trace equivalence.

The native Q, single-shift, zero-homology and functor-associator
comparisons retain the original intermediate objects and their explicit
integer degrees. The original-class comparison is proved before whole
functionals are packaged. No compatibility or perfect-pairing premise is
added by this parent.
