# Original exceptional power sections

Let A be a commutative Noetherian Nagata normal local domain of dimension two
satisfying the existing `NormalModificationH1Vanishing A` predicate. The
ordinary blowup X, full exceptional inclusion i:E→X and coefficient map
κ=A/m→Gamma(E,O_E) are the original constructions from
[Exceptional](../Exceptional.lean). Regular and singular A are both allowed.

`exceptionalPower` is the actual restriction i*(I^n), where I=m O_X is the
original Cartier ideal. `exceptionalPowerTensorIso` identifies it with the
native nth tensor power of L=i*I. The zeroth-power comparison uses the original
unit-module pullback.

`exceptionalPowerSequence` constructs the short exact row

```
0 -> I^(n+1) -> I^n -> i_*L^n -> 0.
```

It tensors the original closed-immersion ideal sequence by the actual
invertible power. Native Cartier multiplication identifies the first term,
and the original closed-immersion projection formula identifies the last.
The first map retains the original inclusion triangle; the quotient map is
proved equal to the original pullback adjunction unit.

The native source `exceptionalPowerLayer` is

```
(m^n) / (m • top : Submodule A (m^n)).
```

Its denominator consists exactly of the elements of m^(n+1). This is the
existing ideal-power quotient with its canonical A/m-module structure and
scalar tower. No replacement grading or section-algebra framework is defined.
The target section module keeps the original structural A-action through
pushforward. Its A/m-action comes from the original exceptional coefficient
map; the proved coefficient triangle supplies the scalar tower.

`ordinaryPowerSectionLinear` sends a to its actual scalar ideal section.
Its bijectivity follows from the original coefficient bijection, the original
normalization inclusion triangle and the normalized section-image
theorem. Thus the source of the global row is identified with m^n by its actual
values, and its kernel is exactly the next power. H1 of I^(n+1) gives the
surjectivity used to construct `exceptionalPowerThetaA`. Extending linearity
along the original quotient A→A/m gives `exceptionalPowerTheta`:

```
theta_n : m^n/m^(n+1) ≃_κ Gamma(E,L^n),  n >= 0.
```

`exceptionalPowerTheta_class` retains restriction of every original scalar
section. `exceptionalPowerTheta_zero` recovers the previously constructed
`exceptionalCoefficientsEquiv` on every original residue class.
`exceptionalPowerTheta_product` uses the native Cartier product and pullback
tensor comparison: the original classes of a and b map to sections whose
product is the section of the original class of a*b. This is a pointwise
product law with the original maps, without an auxiliary graded section ring.

`ordinaryIdealPower_H1` includes degree zero through the honest rationality
predicate. The actual normalized coherent cohomological-dimension bound,
transported through the same original positive-power normalization map,
supplies H2 of each positive ordinary power. The original short exact row
then gives `exceptionalPower_H1` for every n≥0.

The source argument is the exceptional section sequence in
[Stacks 54.9.5, 0B63](https://stacks.math.columbia.edu/tag/0B63).
No coefficient-field section, reduction of E, supplied H0/section isomorphism,
CM predicate, Hilbert function or Gorenstein assumption is introduced.
The projective positive-twist comparison and closed-stalk curve geometry are
subsequent consumers. Degree-two generation remains subject to its separate
nonregularity or genuine degree-at-least-two condition.
