# The same global canonical coefficient as its original local ideal

Source: [LocalIdeal.lean](LocalIdeal.lean).

The complete telescope is that of `NormalSurface.StalkEmbedding`: the
original integral normal surface embedded in the specified finite-coordinate
projective space over the regular local domain, the actual dimension bound
and finite generic-image base map, and an arbitrary original point `x`.
No extra Gorenstein, rationality, rank, finiteness-over-the-parent or completion
premise is introduced.

`normalSurfaceCanonicalLocalIdealIso` starts with the SAME global canonical
module `W` and its actual pullback to `Spec (X.stalk x)`. It uses the native
`stalkFromSpecStalkSectionsIso`, the accepted numerator equivalence for the
ONE chosen global generic frame, the existing specified-section affine
comparison and the inverse of the existing `AffineRow.originalIdealIso`.
Its target is the literal ideal module of the same affine-centre numerator.
No comparison, ideal, denominator or canonical coefficient is rebuilt.

`normalSurfaceCanonicalLocalIdealIso_sections` identifies its actual
inclusion on global sections with the original section/stalk comparison,
SAME numerator equivalence and ideal subtype. The algebra-map and original
germ laws then retain the accepted denominator scaling in the ORIGINAL
`X.functionField`, with the SAME global generic frame.

This is a coefficient comparison on the original local spectrum. It does
not endow an arbitrary later local model with a global projective canonical
object, prove image invertibility, or assert Gorensteinness or resolution.
Those require the original pullback/image geometry and canonical maps.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/LocalImage](LocalImage.md).
