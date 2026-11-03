# Restriction isomorphisms from open sections

[OpenSection](OpenSection.lean) proves
`Scheme.isIso_restrict_of_open_section`: an actual open-immersion section over
a nonempty target open makes the restricted separated morphism from an
integral source an isomorphism. It uses the actual source restriction and the
original section triangle. Properness and curve hypotheses are unnecessary.
The field-graph closure construction consumes the theorem.

[OpenPullback](OpenPullback.lean) proves `Scheme.Hom.isIso_pullback_of_range_subset`: the actual pullback second projection is an isomorphism when the supplied base map has image in an open where the original restriction is an isomorphism. [CartesianRestriction](CartesianRestriction.lean) proves the corresponding inverse-image-open restriction result for any supplied cartesian square and its actual arrows. [BaseChangeRestriction](BaseChangeRestriction.lean) specializes it to the standard pullback.

[StalkBaseChange](StalkBaseChange.lean) detects an isomorphism from
closedness of the original map and invertibility of its actual base changes
to target stalk spectra. Its original-base version retains the model
localization projections. No properness assumption is substituted for
closedness and no abstract stalk isomorphism replaces these maps.
The normalization and local-modification consumers use this criterion.
