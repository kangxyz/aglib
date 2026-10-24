# Literal normalized point-blowup chains

Import `Aglib.AlgebraicGeometry.Surfaces.Resolution.NormalizedPointBlowupChain`.
Declarations belong to `AlgebraicGeometry.Scheme.Blowup`.

For an integral scheme `X` and a closed nongeneric point `x`,
`normalizedPointBlowup X x hx hne` is the normalization of the constructed
ordinary blowup of `(X.fromSpecResidueField x).ker`, in that blowup's original
function field. `normalizedPointBlowupMap` is exactly its normalization map
followed by its original ordinary blowdown.

`NormalizedPointBlowupChain` records a finite sequence of these literal
steps and indexes it by the exact composite arrow. Its constructors store
only the actual closed point, its nongeneric-point proof, and the remaining
chain. `length` counts the specified steps. This type supplies the finite
normalized chains used by completion descent; the separate
`PointBlowupChain` type records ordinary blowups.

Step and chain theorems derive integrality, normality and dominance.
`NormalizedPointBlowupChain.functionFieldMap_isIso` proves birationality
through the original generic stalk map. It composes the actual field maps
of generic normalization and ordinary blowdown.

These constructions require no Noetherian, excellence or Nagata hypothesis.
Finiteness of an inserted normalization does require an additional argument;
the completion-descent consumer derives it from the actual normal-completion
comparison. Accordingly this module supplies no unconditional normalized-chain
properness theorem.

The literal step order agrees with the prescribed sequence in
[Stacks Lemma 54.11.7, tag 0BGA](https://stacks.math.columbia.edu/tag/0BGA):
ordinary point blowup first, then its normalization. The current consumer
assumes a genuine finite upper chain; existence of a complete-local resolving
chain is separate.
