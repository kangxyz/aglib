# Original affine closed-adjoint localization

Source: [Localization.lean](Localization.lean).

This owner compares principal restriction on the supplied injective resolution
with the original exact scalar-extension map on Ext. The public
`closedImmersionQuotientLocalizationHomologyMap_ext` retains the original
source isomorphism, affine restriction coefficient map, and chosen resolution.
It does not assume the desired homology restriction square.

For `closedImmersionQuotientLocalizationHomologyMap_ext`, the ring `R`,
ideal `I` and element `t` are arbitrary. Its coefficient `L` is quasicoherent
and `J` is the supplied injective resolution. The ambient Ext worlds for
`ModuleCat R` and `ModuleCat (Localization.Away t)` are retained independently,
and the degree is natural. No Noetherian or regular-sequence hypothesis is
added to this comparison.

## Original localized quotient presentation

`quotientAwayRingEquiv I t` is the original ring equivalence

    R_t / I R_t ≃+* (R/I)_[t].

Its implementation is unchanged: the proved kernel of the original
`IsLocalization.Away.map` identifies the quotient, and the original surjective
map induces the quotient-kernel equivalence. `quotientAwayRingEquiv_mk` states
its value on a quotient representative using the literal native Away.map.
The original module source comparison uses this same equivalence; no second
ring or module comparison is selected by this export.

The public ring map permits the actual scheme source-isomorphism square to be
formed. Together with the existing original source-homology laws it is intended
to identify canonical quotient and geometric localization presentations in flat
base-change overlap. Exporting this ring equivalence alone does not prove that
overlap, global canonical base change, or arbitrary-field generation.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Canonical/LocalModel/OpenCounit/Sections](../../../../Duality/Projective/Canonical/LocalModel/OpenCounit/Sections.lean), [AlgebraicGeometry/Cohomology/Duality/Projective/Canonical/LocalModel/SourceIsomorphism](../../../../Duality/Projective/Canonical/LocalModel/SourceIsomorphism.lean).
