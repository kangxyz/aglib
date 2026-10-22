# Integral equations and native minima for a specified Weierstrass curve

Let `R` be a commutative domain (`[CommRing R] [IsDomain R]`), and let `F` be
a field supplied with `[Algebra R F] [IsFractionRing R F]`. All coefficient
maps use `algebraMap R F`. Let `W : WeierstrassCurve F` be the original equation. The
algebraic constructions and comparisons between literal cubics over `F`
preserve independent universes for `R` and `F` and work in every characteristic.

`WeierstrassCurve.IntegralModel.denominator R W` is one non-zero-divisor `d`
chosen by Mathlib's common-denominator construction for the five coefficients.
Its actual numerators satisfy `map nᵢ = (map d) aᵢ`. The equation
`IntegralModel.equation R W` over `R` has coefficients

\[
(n_1,\;d n_2,\;d^2n_3,\;d^3n_4,\;d^5n_6).
\]

Thus its mapped coefficients are `Dⁱ aᵢ`, with `D = algebraMap R F d` and
weights `1, 2, 3, 4, 6`. The denominator is nonzero both in `R` and in `F`.
`equation_baseChange` identifies this literal mapped equation with `C • W`,
where `C = denominatorChange R W` is the native admissible change
`(D⁻¹, 0, 0, 0)`. The forward coordinates from the integral generic equation
to the original equation are

\[
 x_{\mathrm{old}}=D^{-2}x_{\mathrm{new}},\qquad
 y_{\mathrm{old}}=D^{-3}y_{\mathrm{new}}.
\]

`genericOverIso` uses the actual quotient, graded, and Proj variable-change
maps, preceded only by the canonical equation-equality cast. Its target is the
same original `W`. `genericOverIso_over` retains the original structural maps;
`genericOverIso_infinity` retains the actual infinity section. The discriminant
has the same native orientation:

\[
 \operatorname{map}(\Delta_V)=D^{12}\Delta_W.
\]

`equation_discriminant_ne_zero_iff` preserves nonvanishing. The integral
discriminant can be a nonunit in `R`, so smoothness of the entire integral
curve is a separate condition.

## The native DVR minimum

When `R` additionally satisfies `[IsDiscreteValuationRing R]`,
`minimalChange R W` is the actual change selected by the
pinned Mathlib theorem `WeierstrassCurve.exists_isMinimal`. `minimalEquation R W`
is the native integral model of that selected equation. Its literal generic
base change is `minimalChange R W • W`, and
`minimalEquationGenericIsMinimal` proves Mathlib's original `IsMinimal`
predicate for it. The native integrality guard and valuation comparison are
retained; no new minimum predicate is introduced.

`minimalGenericOverIso` realizes the selected full native change by a pointed
projective isomorphism to the same original `W`, using the actual
[full coordinate substitution](ProjectiveVariableChange.md). For its scale coefficient
`u`, the discriminant equation is

\[
 \operatorname{map}(\Delta_{V_{\min}})=u^{-12}\Delta_W.
\]

`minimalEquation_discriminant_ne_zero_iff` preserves nonvanishing. The native
minimum producer applies also to zero discriminant. The nonvanishing equivalence
and comparison below state the relevant nonzero conditions explicitly.

## Comparing two native minimum equations

For two literal equations `V, V'` over the same DVR, suppose their mapped
fraction-field equations satisfy the native `IsMinimal` predicate. Given the
actual native change `C` with `C • V_F = V'_F` and `V.Δ ≠ 0`,
`minimal_integral_equations_change_descends` returns an actual native change
`CR` over `R` with both

```
CR.baseChange F = C
CR • V = V'
```

The proof first uses both native maximum conditions to equate the
multiplicative discriminant valuations. The discriminant equation and its
nonzero factor then force the scale to have valuation one. The existing DVR
unit-lifting theorem supplies the original scale as an `R`-unit, and Mathlib's
native `variableChange_integral_of_u_integral` supplies its `r`, `s`, and `t`.
This retains the specified `C` and both original coefficient equations in
every residue characteristic. The nonzero discriminant assumption is essential:
zero discriminant cannot constrain the scale by this argument.

`minimal_integral_equations_pointed_iso` realizes this same descended change
by an actual pointed projective isomorphism `E : curveOver V' ≅ curveOver V`
over the original DVR. Its output retains `CR.baseChange F = C` and
`CR • V = V'`. The defining equality for `E` is the canonical equation cast
followed by `VariableChange.projectiveOverIso V CR`, so the actual original
`CR` supplies its homogeneous coordinates. The original structural maps and
the actual infinity sections over `Spec R` are preserved. This uses the
arbitrary-commutative-ring projective provider; the coefficient universes and
the original native minimality and nonzero-discriminant hypotheses are retained.

## The categorical generic fibre

`genericFibreOverIso` and `minimalGenericFibreOverIso` compose with the existing
canonical coefficient-base-change isomorphism to identify the actual
categorical generic fibre. Their infinity equations use the actual pullback of
the integral infinity section. These separate wrappers retain the existing
base-change API's same-universe boundary for `R` and `F`; the algebraic and
literal-`F`-cubic results above keep their independent universes.

All constructors start from an already specified native Weierstrass equation.
Presenting an arbitrary abstract pointed genus-one curve as such a cubic is a
separate obligation. The minimum statement concerns the native family of
integral Weierstrass equations under native admissible changes over a DVR.
