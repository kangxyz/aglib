# Pullback and tensor insertion of sections

[Basic](Basic.lean) identifies the original section-insertion transformation
with right insertion and proves its pullback equation.
[Naturality](Naturality.lean) changes the other coefficient through the
given original map. These statements allow arbitrary module sheaves,
with the native tensor units and pullback comparisons.

[LineTensor](LineTensor.lean),
[ComposedCoefficient](ComposedCoefficient.lean),
[ComposedLineTensor](ComposedLineTensor.lean) and
[ComposedPullbackLineTensor](ComposedPullbackLineTensor.lean) retain the
supplied line bundles, composition triangles and coefficient equations.
No Cartier divisor, blowup, flatness or surface hypothesis is introduced.
The regular-pair and exceptional-line calculations use these same section
maps.

Present consumers include [Relative forms on a two-generator ideal blowup](../../../../Blowup/Differentials/PairIdeal/README.md), [Relative forms on saturated regular-pair charts](../../../../Blowup/Differentials/RegularPair/README.md).
