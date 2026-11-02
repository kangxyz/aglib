# Determination and gluing of maps into a line

[Open](Open.lean) determines maps into an actual line bundle on an integral
scheme from their restriction or pullback to a nonempty open immersion.
The source module is arbitrary.

[OpenPrecomposition](OpenPrecomposition.lean) proves injectivity after
precomposition by an arrow invertible on one nonempty open.
[OpenGluing](OpenGluing.lean) derives compatibility from the stated unit
squares and uses the original internal-Hom gluing on an actual open cover
to construct the unique global map. The same native overlaps and line
target are retained. Ideal-blowup one-pole maps use this uniqueness and
gluing interface.

Present consumers include [Relative forms on a two-generator ideal blowup](../../../Blowup/Differentials/PairIdeal/README.md), [Universal blowups and saturated affine charts](../../../Blowup/README.md).
