# Actual extension points under coefficient-fixing automorphisms

`ExtensionPointAction.lean` uses the existing native affine coordinate-ring
maps, affine scheme points, and infinity section. A field automorphism fixing
the specified original-field map acts by literal precomposition with its
`Spec.map` arrow. The ring-map and scheme-map equations preserve the actual
coordinates and original base structure. The field-extension spectrum map is
provided separately by `RationalPoint/FieldAutomorphism.lean`.

Both fields retain their original common universe. There are no characteristic,
norm, completion, period, or analytic-coordinate assumptions in this slice.
