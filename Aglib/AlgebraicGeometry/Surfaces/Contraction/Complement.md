# Original mixed coordinates on the exceptional complement

This module consumes the fixed actual section presentation and image construction
from `ProjectiveImage.lean`. The original input remains a closed projective
embedding over a Noetherian base with a finite coordinate labeling
`ι ≃ Fin (r+1)`, the given ample-line comparison, the original
invertible Cartier ideal, and the given native projective-line comparisons.

`offExceptionalProjectivePowerIso` works over any actual morphism `g : T -> X`
whose point image misses the original exceptional curve. It uses the original
pulled common Cartier inclusion, the given ample power comparison, and the
original pullback-composition map. `mixedCartierSection_offExceptional` cancels
that actual common multiplier and retains each original mixed homogeneous
section. `offExceptionalCocycleIso` records the original pulled projective
cocycle comparison.

`offExceptionalFrames` gives actual original-diagonal frames for the original
pulled finite section family. Its coefficients are the original pulled
homogeneous chart functions. `offExceptional_toProjective_eq` identifies their
actual native projective morphism with the original source composite, retaining
the same coordinate index and original section maps.

`offExceptional_preimage_diagonal` identifies each new diagonal-coordinate
preimage with the original old-coordinate preimage. It uses the actual mixed
and diagonal-power coefficients; no characteristic restriction is needed.
`residueCoefficient_mixed` and `residuePoint_preimage_diagonal` retain the actual
vanishing on E for `nd>=1`. Consequently `diagonalSource_disjoint` proves that
the original preimage of each new diagonal chart really misses E.

`toImage_schemeTheoreticallyDominant` proves the genuine kernel equality for
the original proper map to its actual schematic image. This supplies the
scheme-level input for restricting to open image charts. The local recovery
map and its scheme-level complement inverse are constructed below. The actual
first-order ideal comparison remains a subsequent construction. No normality or structure-sheaf
pushforward equality is assumed from the raw image construction.

For an actual residue field, `residuePoint_isClosedImmersion` applies the full
original coefficient-span theorem to the same native `Spec k` projective map.
`residueToImage_isClosedImmersion` retains that original field point inside the
actual kernel image, with its existing triangles. Its inputs are the proved
restriction-map surjectivity and a chosen original unit coefficient; they are
provided for sufficiently large n by the actual cohomological construction.
No rationality or characteristic premise is introduced.

`mixedBaseChartLift` and `mixedBaseChartMap` retain the original coefficient
ring and send each original old-chart ratio to its prescribed new mixed ratio.
`diagonal_recovery` states the resulting equality of the actual scheme
morphisms, after restricting the original new map to a diagonal chart.
`diagonal_isClosedImmersion` uses that recovery and actual properness.
`toImage_diagonal_isIso` combines it with the original kernel-image map's
schematic dominance. `imageComplement_restrict_isIso` glues those local
isomorphisms on `imageComplementOpen`, the union of the actual image charts.

`toImage_preimage_imageComplement` proves that the preimage of this image open
is literally the original `exceptionalComplement`. `complementIso` therefore
provides an actual scheme isomorphism, with both original-map triangle formulas.
`imageComplement_carrier` identifies its target open with the complement of the
entire original `Spec k` image, using actual proper-map surjectivity. In the
field case the same original residue map is the closed immersion proved above.

`exists_cartier_projective_complement` obtains these objects for every
sufficiently large n from the original cohomological constructions, assuming
`IsField k` and `0<d`. It chooses n with `nd>=2`, retains the full residue-field
span and every prescribed mixed coordinate, and retains the two actual proved
first-order lifts as literal coordinates of the same finite family. The
conclusion includes the actual image-point map and actual complement inverse.
It does not assert structure-sheaf pushforward equality, the equality between
the pulled image-point ideal and the exceptional Cartier ideal, target
normality, or target regularity. Those require the original first-order ideal
and formal-functions arguments.
