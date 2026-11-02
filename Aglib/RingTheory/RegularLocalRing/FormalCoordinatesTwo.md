# Original formal coordinates in characteristic p and dimension two

Source: [FormalCoordinatesTwo.lean](FormalCoordinatesTwo.lean).

`IsRegularLocalRing.exists_formalCoordinatesTwo_of_charP` starts from the
ORIGINAL complete regular local ring R of dimension two in prime characteristic.
It chooses the existing coefficientSectionOfCharP and an actual length-two
regular generating sequence of the maximal ideal. The native evaluation lower
then gives a ring equivalence from the two-variable power-series ring over the
native residue field to this SAME R, including constants, variables and residue
equations. No perfectness or finite absolute p-rank is assumed.

The original R and its fraction field must not be replaced by a merely finite
subring: that could change a strict degree used by resolution induction. A later
consumer transports the integral differential basis to R and applies the
existing fraction-basis theorem to the ORIGINAL fraction field. Its coefficient
base is the genuine expanded series base, not just the residue field.

Direct consumers: [RingTheory/Kaehler/PureDegreePTrace/CompleteRegularEntrance](../Kaehler/PureDegreePTrace/CompleteRegularEntrance.md).
