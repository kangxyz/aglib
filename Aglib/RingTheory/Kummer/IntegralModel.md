# Literal Kummer integral models from UFD exponents

`IntegralModel.lean` exposes `Algebra.Kummer`.

For a UFD domain with a supplied normalization monoid and specified fraction field, signed
normalized factor exponents divisible by n give an actual unit-times-nth-power decomposition.
The polynomial quotient, scaling isomorphism, tensor generic-fiber comparison, and
factorization statements retain level zero where the source permits it. At positive levels
invertible in the base, the literal unit-root algebra is finite and etale. Over the stated
integrally closed base with its specified fraction field, its canonical generic comparison
identifies it with the literal integral closure in the original parameter-root algebra.
This comparison and its generator, finite and etale consequences require no Noetherian
hypothesis. The final factorization application retains its domain, UFD and normalization-monoid
hypotheses. No regular-local factoriality, purity or arithmetic realization is asserted.

The arbitrary-parameter carrier is the literal Mathlib `AdjoinRoot (X ^ n - C f)`.
At a unit parameter it is definitionally the same polynomial quotient used by the
existing RootCover family; the pure-ring module does not import that scheme layer.
The normalization comparison uses the actual canonical `Algebra.FiniteEtale.GenericMaps.modelEquiv`.

Source: `R5Lab.Aglib.RingTheory.Kummer.IntegralModel`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`b4f8c119e6fb31b535808fd196fe83f9c35a4b4ca8e0135eb4036e46ae9b463a`.

Source correspondence and compilation coverage have separate records in the assigned
scratch handoff; this document does not assign mathematical closure status.
