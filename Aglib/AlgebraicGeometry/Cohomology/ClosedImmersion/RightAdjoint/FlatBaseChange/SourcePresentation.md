# Original localized quotient source

Source: [SourcePresentation.lean](SourcePresentation.lean).

For a commutative ring R, ideal I and t in R, this leaf uses the ORIGINAL
`quotientAwayRingEquiv` from the original localization owner. Its actual ring
triangle yields the identity-ambient Cartesian square between R_t→(R/I)_t
and R_t→R_t/I_t. The closed-immersion instances follow from the actual
surjective quotient/localization maps; no Noetherian assumption is added.

`quotientAwaySourceModuleIso_comp` identifies the actual canonical tensor
source map followed by the original `closedImmersionSourceModuleIso` with the
original `closedImmersionQuotientLocalizationSourceIso`. It uses only their
original representative/unit laws, not a second source comparison.

On the SAME supplied injective resolution J, the Ext equation and inverse
cancellation specialize the existing `closedImmersionSourceHomologyMap_ext`
and `_ext_cancel`. These require quasicoherence of L and the native HasExt
world of R_t. They add no finite, flat, regular-list or Gorenstein assumption.
The every-open sheaf-homology equation specializes the existing original
affine-counit law and needs neither quasicoherence nor HasExt.

The current three homology/counit statements spell out their original module
`L : (Spec A).Modules` and supplied injective resolution `J` directly in each
header, retaining the same ambient/source rings, quasicoherence and independent
Ext universe. Their original maps and proof bodies are unchanged.

The two original closed-immersion instances are public so that the public
homology statement headers can use them under Lean's exporting elaboration.
`quotientAwaySource_closed` derives surjectivity from the actual localized
quotient map; `quotientAwayCanonicalSource_closed` uses the actual quotient
surjectivity. Their native proofs and maps are unchanged. They add no assumed
closed-immersion hypothesis. Private declaration probes could use the former
private instances, whereas public headers cannot; this visibility distinction
is separate from earlier constructor type-formation diagnostics.

## Literal quotient-localization arrow

`quotientAwaySourceLocalizationRingTriangle` compares the canonical quotient
algebra map with the principal quotient arrow using the SAME quotientAway ring
equivalence. `quotientAwaySourceLocalizationSpecMap` derives equality of the
original spectrum arrows by inverse cancellation and native Spec composition.
Their proofs use the native quotient algebra-map value, original representative
law, and original Away.map value; no new scalar action or source model is chosen.
