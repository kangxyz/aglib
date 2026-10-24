# Finite constant roots in an actual rational extension

`IsPurelyInseparable.exists_finite_constant_field` starts with fields
`K`, `F`, `L` and `Ω`, an algebraically closed `Ω`, and the compatible
original maps `F → L → Ω` and `K → Ω`. The extension `L/F` is finite and
purely inseparable. The specified `p` is an exponential characteristic of
both `K` and `F`, and `t : Ω` is transcendental over `K`.

The explicit rational-presentation input says that every original image of
`x : F` is `a(t)/b(t)` for some `a,b : K[X]`, using the specified `K → Ω`.
No separate rational-field isomorphism or `K`-algebra structure on `F` is
an input. The conclusion gives a finite purely inseparable intermediate
constant field `E/K`, an exponent `e`, and an element `z` with
`z^(p^e) = t`, with `z` transcendental over `E`, such that the original
image of `L` lies in the literal field `IntermediateField.adjoin E {z}`.
The actual coefficient and extension maps into `Ω` are retained.

The proof takes inverse Frobenius roots of only the finitely many coefficients
used by the numerator and denominator presentations of powers of a finite
basis. It makes no assumption on the imperfection degree of `K`. Exponential
characteristic one includes characteristic zero.

The polynomial Japanese consumer supplies the literal field of fractions of
the original polynomial ring, and obtains the rational presentations directly
from its fractions. Thus no field identification changes the coefficient map.

[Nagata.Polynomial](../../RingTheory/Nagata/Polynomial.md) imports this
finite-constant theorem. It is separate from
[RationalFunction](RationalFunction.lean), which supplies the perfect
rational-function extension over separably closed constants.
