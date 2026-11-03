# Original function fields in a target-stalk square

Source: [BaseChange.lean](BaseChange.lean).

`functionFieldMap_square_of_isPullback_fromSpecStalk` records the literal
field-map square of an actual Cartesian square along X.fromSpecStalk x.
The schemes are integral and the three actual model maps dominant. No
birationality premise is needed for this equality.

`functionFieldMap_isIso_of_isPullback_fromSpecStalk` adds invertibility of
the original map on function fields. The original projection is flat and
preimmersive by the square, so its original generic-stalk map is invertible.
The original local-spectrum field map is also invertible. The existing
cancellation body from RegularTarget then proves the local model's actual
field map invertible. The old rationality consumer delegates to this owner.

No replacement fraction field, arbitrary field identification, properness,
Noetherianity, normality, dimension or rationality is used. The literal
LocalStages consumer derives all geometric hypotheses on its native pullback.

Direct consumers: [AlgebraicGeometry/Surfaces/RationalSingularities/ModelLocalization](../../Surfaces/RationalSingularities/ModelLocalization.md), [AlgebraicGeometry/Surfaces/RationalSingularities/RegularTarget](../../Surfaces/RationalSingularities/RegularTarget.md), [AlgebraicGeometry/Surfaces/Resolution/NormalizedPointBlowupChain/LocalStages](../../Surfaces/Resolution/NormalizedPointBlowupChain/LocalStages.md).
