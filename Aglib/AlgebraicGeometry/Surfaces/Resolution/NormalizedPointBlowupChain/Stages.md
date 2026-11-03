# The actual stages and cuts of a normalized-point chain

Source: [Stages.lean](Stages.lean).

This lower leaf adds finite-index accessors to the EXISTING
`NormalizedPointBlowupChain`. It constructs no new chain type or replacement
scheme. `stage`, `toBase` and `fromTop` recurse through the existing constructors;
`prefix` and `suffix` use those same constructors and exact original arrows.
Their lengths are the cut index and the remaining length, and their composite
is the original total morphism.

`stage_zero` and `stage_last` identify the actual endpoint scheme expressions.
Their only transports are native equality morphisms. A tail's zero-stage
expression need not be definitionally its original base, so the selected step
explicitly retains that equality transport rather than guessing definitional
identity. The successor-prefix and successor-suffix equations account for it.

At each original step, `center`, `center_isClosed`, `center_ne_genericPoint`
and `stepIntegral` recover the data already stored by the native constructor.
`ordinaryDatum` is the original residue-point ideal blowup. `normalizationMap`
is its original generic-normalization arrow after only the endpoint equality;
`normalizationMap_comp` proves that it followed by the original ordinary
blowdown is precisely the selected step.

No initial integrality premise is needed just to inspect an empty chain.
Integrality at each actual nonempty step comes from that constructor.
No Noetherianity, properness, normality, dimension, projective embedding,
canonical coefficient, cohomology, regularity or resolving-chain existence
is added to the accessor telescope.

Later geometry may use the actual prefix/suffix chains to DERIVE properness
and original function-field comparisons. A singular trajectory consists of
images under `fromTop`, not a supplied arbitrary point list. The later
canonical embedding family must handle length zero separately if its two
supplied endpoint embeddings differ; this leaf does not identify embeddings.

Direct consumers: [AlgebraicGeometry/Surfaces/Resolution/NormalizedPointBlowupChain/SupportedStages](SupportedStages.md).
