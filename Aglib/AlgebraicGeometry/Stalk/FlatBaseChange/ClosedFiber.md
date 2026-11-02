# Actual closed singular fibres under flat preimmersion base change

For the same pullback square with flat preimmersion base map `j`,
`closedSingularFiberEquivOfIsPullback` identifies the globally closed singular
points over an actual point `x` and its image `j x`. The image root must be
globally closed. Its forward map is exactly the original projection `c`;
the inverse retains both actual point projections.

The closed-image proof uses the native whole-fibre image equation from
`Scheme.image_preimage_eq_of_isPullback`. That closed fibre is contained in
the range of the original preimmersion. The existing inducing-map theorem
expresses the image of a closed singleton as a closed set intersected with
that range; intersecting with the actual closed fibre proves global
closedness. Closedness inside an arbitrary chart is not silently promoted.

Fibre surjectivity uses `Scheme.exists_preimage_of_isPullback` on the same
square. The actual projection is a flat preimmersion, so its original stalk
map is an isomorphism and preserves regularity in both directions. No new
stalk realization or replacement coefficient map is used.

No Noetherianity, normality, integrality, dimension, finiteness, completeness,
marking or termination hypothesis is needed or concluded. The closedness
lemmas themselves only require the preimmersion, not flatness.
