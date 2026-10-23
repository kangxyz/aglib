# Sections of normal integral schemes

[GlobalSections.lean](GlobalSections.lean) proves normality of the actual section
rings of an integral scheme. The canonical map is
`Scheme.germToFunctionField`, with codomain the actual stalk at the generic
point.

- `Scheme.isIntegrallyClosedIn_functionField_sections X U hNormal` proves
  `IsIntegrallyClosedIn Γ(X, U) X.functionField` for any nonempty open `U` whose
  actual stalks are integrally closed.
- `Scheme.isIntegrallyClosed_sections X U hNormal` gives integral closedness of
  this section ring in its own fraction field. The domain condition is already
  Mathlib's `IsIntegral.component_integral` instance.
- `Scheme.NormalStalks.isIntegrallyClosed_globalSections X hNormal` gives
  `IsIntegrallyClosed Γ(X, ⊤)` from integrality of `X` and `NormalStalks X`.
  Mathlib also supplies `IsDomain Γ(X, ⊤)` under this integrality hypothesis.

An element of the function field integral over the section ring is integral
over each stalk through the canonical section-stalk-function-field tower.
Normality of that stalk supplies a representative. Representatives are realized
on neighborhoods and restricted inside `U`. Their images in the function field
agree; stalk injectivity proves compatibility on intersections. The actual
structure sheaf then glues them over `U`. Injectivity of the section map into
the field transfers this closure statement to the section ring's fraction
field.

No affine, Noetherian, proper, dimension, coefficient-field, separability or
excellence hypothesis is used. The function field is not assumed to be the
fraction field of the global sections. Nonemptiness of the open is explicit;
the global theorem obtains it from integrality.

The gluing pattern is already present in
[the curve-divisor section extension](../../Curves/Divisors/RegularSections.lean),
but this lower module does not import the curve theory or introduce a duplicate
public gluing theorem. Its new conclusion is integral closedness.

Source basis: Aglib `22f7532679eec4295167fcf885cf8b1b0981d899`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1. New formalization;
native compilation is coordinated by the root task. This result supplies the
normality-of-global-functions step, with no claim about the remaining surface
contraction argument.
