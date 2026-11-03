# The original fraction fields of the expanded-base square

For the given coefficient inclusion `E → k` and a nonzero exponent `q`,
`scalarMap` sends `E[[U,V]]` to the original `k[[u,v]]` by the coefficient
map followed by expansion. `scalarMap_injective` proves injectivity from
the coefficients at q-divisible exponents.

Write `Λ = E[[U,V]]`, `A = k[[u,v]]`, `K₀ = FractionRing Λ`, and
`K = FractionRing A`. `seriesFractionMap` is the original `Λ → A → K`.
`fractionBaseMap` is its unique induced map `K₀ → K`; the equation on
original base series is `fractionBaseMap_algebraMap`. The two named scalar
algebras and their `IsScalarTower` theorems retain these exact maps.

In characteristic `p`, let `F ⊂ k` be the actual chosen subfield containing
the Frobenius image. `frobeniusBaseSeries` regards each pth-power coefficient
of the original series as an element of `F`.
`scalarMap_frobeniusBaseSeries` proves that its image is the original
series's pth power. Infinitely many coefficients are retained; no finite
p-rank assumption is used.

Let `S` be the nonzero elements of `Λ` and let `T` be their actual image
submonoid in `A`. Every nonzero denominator `b` in `A` has `b^p ∈ T`, so
`a/b = (a*b^(p-1))/b^p`. `fraction_isLocalization_image` therefore proves
that the existing A-algebra `K` is the localization of A at T. It does not
give or require `IsFractionRing Λ K`; the base fraction field remains K₀.
The generic `IsFractionRing.isLocalization_of_power_mem_range` proves the
same denominator argument for any fixed positive exponent and the original
injective ring map.

`fraction_D_ne_zero` instantiates the literal Kähler localization map for
this square. A nonzero ordinary differential in a supplied constructed
basis remains nonzero in `Ω[K/K₀]`, because the actual denominators have
nonzero images in the domain A and hence act injectively on the free
module. No continuous or completed differential module is used.

`exists_singleSeries_fraction_base` applies this transport to the actual
rank-two and rank-three branches constructed in `Differentials` for a
given non-pth-power series. It retains the top coefficient field in the
spatial branch and the same selected coefficient and maximal avoiding
subfield in the coefficient branch. The input has no differential-basis
or nonzero-differential hypothesis; those are obtained from the earlier
construction. Characteristic two and fields of infinite p-rank are included.

The current consumer is the single-series entrance to the purely
inseparable degree-p B7 argument. Higher trace, canonical-module
identification, and the uniform cohomology bound remain downstream. This
construction is separate from the full fixed-p-basis family/intersection
theorem.

The mathematical square is recorded in the principal-read packet
`ORIGINAL_FRACTION_SQUARE.md`, SHA256
`42523bb2db6e7840ba400dec691dbbdd9a6b869321ef27b9059e76c5ea93ae24`,
and its initial proof script
`2c42e87ae17b8452dd9d15717911c54a72c126f98967301078d77cd9f6968d9b`.
The historical source basis was release HEAD
`f27c5fa9b8f76147e16caacf52f56f26eabddb87`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and Lean 4.34.1.
Compiler coverage is recorded by the principal's shared native batch.

## Unchanged-base localization bridge

`KaehlerDifferential.fractionBasis` transports any actual A-basis of ordinary
Ω(A/Λ) to Ω(K/Λ) through `(b.baseChange K).map e`, where e is the native
formally-étale tensor equivalence for the original fraction localization.
`fractionBasis_repr_D` proves that each coordinate of d(image a) is precisely
the original A-coordinate mapped to K. Thus `finrank_fraction_of_basis`
preserves the finite basis cardinality, and `fraction_D_ne_zero_of_basis`
preserves nonzero differentials by injectivity of A → K. Neither separability
of K over a constant field nor a replacement of Λ by Frac(Λ) is assumed.
These are the direct inputs for the positive-rank trace consumer in Cokernel.
The earlier K/K₀ results remain separate statements with their explicit base.

`exists_singleSeries_fraction_basis` combines this transport with the actual
series entrance: one E, one positive r, finite A over the expanded Λ, the
original integral differential basis, generic dimension r, and nonzero df
in Ω(K/Λ). It does not use the distinct K/K₀ branch to feed the trace.

## Native verification

The current source, including the two algebra-instance docstrings, has SHA-256
`bf7c1f54f7f82ac2f4c9fdb9f42fb0925a21bdd75039d6568465eb2639e7ce52`.
It passed the coordinated native rebuild, upstream declaration lint and
pinned production axiom audit. The docstring correction changed no algebra
structure, map, theorem statement or proof body. These are selected-leaf
checks, not a whole-project verification claim.
