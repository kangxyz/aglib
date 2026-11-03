# Unchanged open of the literal normalized point step

Source: [NormalizationAway.lean](NormalizationAway.lean).

`genericNormalization_isIso_restrict_of_normal_open` identifies the actual
generic normalization over a nonempty normal open by the native generic
normalization pullback comparison and trivial normalization of a normal
integral scheme.

`normalizedPointBlowupMap_isIso_restrict_away` applies this to the actual
ordinary point blowup. The original full reduced point ideal has singleton
support, so the ordinary map is invertible on the supplied open avoiding
the centre. Its source there is normal via actual stalk-map isomorphisms;
the original normalized composite is therefore invertible on that open.
No normalization-finiteness or properness assumption is used.

These are the unchanged-complement equations needed in supported-chain
induction; the consumer is now implemented in `SupportedChain`.

Direct consumers: [AlgebraicGeometry/Descent/LocalModification/SupportedChain](SupportedChain.md).
