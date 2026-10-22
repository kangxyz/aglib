# Sections of the original positive point divisor

[Sections.lean](Sections.lean) starts with the actual smooth proper,
geometrically connected field curve `X`, its original rational section
`p : Spec k → X`, the original section equation, and coherent genus one.
There is no group law, Picard representability, algebraic-closure,
characteristic or norm assumption.

`idealLineBundle` is the actual kernel ideal of `p`, with rank one proved
by the native smooth relative-Cartier theorem. `positiveLineBundle` is its
actual dual, and `poleLineBundle n` is its native tensor power `O(np)`.
`positiveSection` is literally the native transpose of the original ideal
inclusion. `inclusion n` tensors it with the identity of `O(np)` through
the canonical unit map. It is monic: the native dual evaluation recovers
the original ideal inclusion, and tensoring by an invertible module is an
equivalence. `sectionsInclusion` is the resulting injective map on actual
global sections, linear for the original structural action of `k`.

`cohomology` proves actual `H¹(O(np)) = 0` and dimension `n` for actual
`H⁰(O(np))` whenever `n > 0`. `sections_finrank` gives the same dimension
on actual global sections via the native degree-zero cohomology comparison.
The point dual has degree one by the proved finite-Cartier degree theorem
and the original rational section equation; tensor powers retain degree
`n`. All-field smooth curve duality identifies the dual of the original
H¹ with H⁰ of the canonical bundle tensored with the original dual. Its
degree is negative for positive `n` on a genus-one curve, so native
negative-degree vanishing kills it. Riemann–Roch then gives the dimension.
Algebraic closure is unnecessary because smoothness is already given on
the original curve.

`oneSection` is the original constant-one positive section in the first
native pole space, using only its canonical tensor-unit comparison.
`oneSection_evaluate` identifies it as the original point-ideal inclusion
on every original global ideal section. It is nonzero and
`oneSection_spans` proves that it spans the actual first pole space.
These flags are the intrinsic input for choosing pole-bound coordinates
at levels two and three and later studying their relation at level six.
No plane-cubic or Weierstrass presentation is asserted here.
