# A prescribed normalized point step under model localization

Source: [NormalizedPointLocalization.lean](NormalizedPointLocalization.lean).

`Scheme.Blowup.normalizedPointLocalizationIso` compares the literal upper
normalized point blowup with the pullback of the literal lower normalized
point blowup along a flat preimmersion `g : Y ⟶ X` of integral schemes.
The supplied upper point is closed and nongeneric; its actual image is also
required closed and nongeneric. `PointLocalization` supplies the closedness
condition in the original proper local-model square.

The full point ideals agree under pullback by the original residue-point
square. Ordinary blowup flat base change gives the actual comparison map
between the ordinary blowups. That map is a flat preimmersion. Its nonempty
source meets the generic point by the generalizing property of flat maps,
so it is dominant. `genericNormalizationPullbackIso` therefore compares the
original generic normalizations. Pasting these two actual cartesian squares
constructs the final normalized-point comparison.

`normalizedPointLocalizationIso_hom_snd` identifies the original upper
normalized blowdown. `normalizedPointLocalizationIso_hom_fst_comp` preserves
the other original projection equation. No finite-normalization premise is
inserted, and no finiteness or properness conclusion is asserted by this
comparison alone. Global finiteness/properness and the full prescribed-chain
induction remain separate obligations.

## Remaining properness obligation

The native `NormalizedPointBlowupChain` datatype carries neither properness
nor finiteness certificates. A globalization theorem must retain a separate
actual proper-total-map hypothesis (as produced by completion descent), not
infer it from the chain alone. A proper tail can be obtained from that total
map only after establishing separatedness of its intermediate structural
map, using `IsProper.of_comp`.

A source-grounded route to global finiteness is to spread the actual proper
normal terminal local model together with its specified factorization through
the first ordinary blowup. Once the resulting global factor is proper,
normal, integral and birational, the existing
`genericNormalization_isFinite_of_proper_birational` supplies finiteness of
the literal generic normalization. The comparison in this file then
identifies its original localized step with the prescribed local step.
This avoids falsely deducing finite generation on a neighborhood from finite
generation after a single stalk localization. Alternatively `FiniteShrink`
proves the proper-source bad-locus shrinking step for an already constructed
factorization with finite actual local base change.

Spreading the factorization and the supported serial induction are now
implemented and natively verified in `FactorReplacement`,
`FactorNormalization`, and `SupportedChain`.
An alternative use of the blowup universal property would require local
rank one of the actual *image* ideal, not merely the tensor pullback of its
module. The factorization route is implemented; the image-ideal route is not needed.

Direct consumers: [AlgebraicGeometry/Descent/LocalModification/ChainTransport](ChainTransport.md), [AlgebraicGeometry/Descent/LocalModification/SupportedChain](SupportedChain.md).
