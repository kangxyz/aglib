# Original affine presentation-unit extensionality

Source: [PresentationUnits.lean](PresentationUnits.lean).

`affinePresentation_unit_ext` detects equality of maps from the original affine
pullback using its geometric unit on sections supplied by an arbitrary original
tilde presentation. The rings, module and sheaves retain their native universe u.
The target sheaf is arbitrary; no quasicoherence, flatness, finiteness or
Noetherian hypothesis is added.

The proof precomposes with the actual pullback of the given presentation iso,
then uses injectivity of the two existing geometric and tilde Hom adjunctions.
It does not construct another adjunction, chosen module model or general
extensionality backend. The original section map is evaluated through the
existing pushforward/global-sections bridge, moved unchanged to [PushforwardSections](PushforwardSections.md).

The native presented-map unit formula is in Nonflat/AffineSheafUnit. The actual
composition theorem consumes its unit formula and this extensionality law.

Direct consumers: [AlgebraicGeometry/Cohomology/BaseChange/HigherDirectImage/Nonflat/AffineSheafUnit](../../../Cohomology/BaseChange/HigherDirectImage/Nonflat/AffineSheafUnit.md).
