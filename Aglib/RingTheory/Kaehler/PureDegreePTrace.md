# The degree-p one-form differential trace

The original algebra `S` carries an explicit
`IsAdjoinRootMonic S (X ^ p - C a)`. The coefficient ring has characteristic
`p`, with `p` prime, and the differential base is an arbitrary scalar tower
`Λ → R → S`. No smoothness, field, finite p-rank, or nonzero `da` hypothesis
is used. Characteristic two is included.

`pureDegreePDerivation` descends polynomial differentiation through the
original presentation. `pureDegreePDifferentialEquiv` is its native Kähler
lift `KaehlerDifferential R S ≃ₗ[S] S`, whose inverse sends `s` to `s dz`.
`pureDegreePCoeff` extracts the coefficient of `z^(p-1)` using the existing
monic coefficient representation.

`pureDegreePTraceOne` is the literal composite

```text
Ω[S/Λ] → Ω[S/R] → S → R → Ω[R/Λ].
```

Its first arrow is `KaehlerDifferential.map Λ R S S`; its last sends `r` to
`r • D Λ R a`. The trace kills every `S`-multiple of a pulled-up form. On
`z^i dz`, for `i<p`, it is zero unless `i=p-1`, when it equals `da`.
`pureDegreePTraceOne_unique` proves uniqueness on the actual differential
module. Its extensionality supplier allows an arbitrary target `R`-module,
which is needed for the scalar-change comparison.

The coordinate calculation is proved by private polynomial coefficient
identities. The top identity is lifted to an integer polynomial ring, where
cancellation by `p` is valid, and then specialized to characteristic `p`.
Lower powers use the fact that `i+1` is a unit for `i<p-1`.
`pureDegreePTraceOne_pow_smul_D_of_pow_eq` then proves the same formula for
any original element `s` satisfying `s^p=c` with `c` in the coefficient ring.
No coordinate-compatibility assumption is supplied.

`pureDegreePTraceOne_naturality` identifies the actual Kähler maps for maps
between degree-p presentations. `pureDegreePTraceOne_baseChange` proves the
corresponding equation for a scalar square; the target presentation may use
any coordinate. The target coefficient ring is also explicitly assumed to
have characteristic `p`.

`pureDegreePTraceOne_localization` identifies the trace on the actual localized
algebra with `IsLocalizedModule.mapExtendScalars` of the original trace. Its
localization instance comes from the native Kähler localization instance and
restriction of scalars. The ring localization uses the canonical image
`Algebra.algebraMapSubmonoid S U` of the original submonoid. The characteristic
assumption on the localized coefficient ring includes all nonzero domain
localizations needed by the height-one consumer.

The matching source construction is Stacks, Section 54.2, especially
[0ADZ](https://stacks.math.columbia.edu/tag/0ADZ) and
[0AX5](https://stacks.math.columbia.edu/tag/0AX5). Ordinary field trace is not
used. The immediate consumer is the exterior differential trace.
[Monogenic](../DiscreteValuationRing/PureDegreeP/Monogenic.md) supplies actual
finite pure degree-p DVR presentations under its stated hypotheses.
Coherent double-dual sheaf extension, canonical-module and proper-trace
compatibility, and the uniform H1 bound remain separate geometric consumers.
