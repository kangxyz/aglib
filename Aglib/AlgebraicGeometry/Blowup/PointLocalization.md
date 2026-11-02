# Original point blowups over their actual local spectra

The input is any scheme X, an actual closed point x, an arbitrary original
universal blowup datum B of the residue-point centre, and an actual closed
point y of B lying over x. There are no Noetherian, integral, normal,
regularity, dimension, arc, marking, or completeness hypotheses.

The local model is the existing ordinary maximal-ideal blowup of the
original stalk X_x. The comparison is exactly the existing BaseChange.map
formed from the original fromSpecStalk map and the proved equality of the
actual pulled-back centre. No new comparison constructor is introduced.
The native flat-base-change theorem supplies its Cartesian square; both
forward projections of that same square's isoPullback are retained.

The native pullback point theorem lifts the pair (y, closedPoint X_x).
The inverse of the same isoPullback gives the actual local-blowup point z,
with both projection equations. Its closedness follows from the original
comparison's preimmersion, not from chart maximality or a dimension bound.

The stalk isomorphism is the right component of the existing complete
flat-preimmersion stalk-arrow comparison. Its forward arrow is explicitly
the original pointLocalRingMap of the comparison. The final commuting
square identifies that arrow composed with the original blowdown
pointLocalRingMap with the literal local-blowup stalkScalar. It uses the
original local-spectrum factorizations and monomorphism cancellation.

Arc.MarkedPath is imported solely to reuse its existing original
pointLocalRingMap and factorization law. No arc or marked path is an input.
The shared PrincipalBaseChange factorization is exposed at its original
owner without copying or moving its proof. This endpoint does not replace
an ordinary scheme path with localizations, assert child completeness, or
identify normalized blowups with ordinary blowups.
