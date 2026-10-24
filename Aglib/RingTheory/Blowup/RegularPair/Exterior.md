# Exterior forms on an original regular-pair chart

Let Lambda -> R -> B be the original coefficient maps and let
`B = R[t]/(x*t-y)`. The actual Kähler scalar map is

```text
f : B tensor_R Omega_(R/Lambda) -> Omega_(B/Lambda).
```

The original chart presentation proves that every differential is
`f(p) + a*dt` and that

```text
x*dt = f(1 tensor dy - t tensor dx).
```

The native cyclic-cokernel exterior lemma consequently puts `x*alpha`
in the image of `exteriorPower.map n f` for every raw exterior form
`alpha`. The result includes degree zero and characteristic two and
requires no freeness, finite-generation, or torsion-free premise on
the differential modules.

The general presentation theorem applies to an actual `IsAdjoinRoot`
presentation. The literal `pairQuotient` specialization uses its original
algebra structure. The saturated blowup-chart specialization uses the
proved `pairChartEquiv` and retains the two regular-pair hypotheses:
`x` is regular on `R`, and `y` is regular on `R/(x)`.
`baseChangeExteriorImageBound` packages the same displayed formula with
its original ring and module instances; the saturated theorem is its
direct specialization, still quantifying over every degree and raw form.

The current geometric consumer is the one-pole inclusion for the double
dual of top relative forms on a regular surface-point blowup. This
family supplies its raw exterior image bound. It does not identify the
pulled-back determinant with the determinant of the pulled-back forms;
their possible effective determinant defect remains relevant.
