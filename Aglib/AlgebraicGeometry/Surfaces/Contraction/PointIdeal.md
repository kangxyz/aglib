# The same image-point ideal and the exceptional Cartier ideal

The original point is the actual `Spec k` map into the same native kernel image
constructed in `ProjectiveImage.lean` and retained in `Complement.lean`. No new
point, residue field, image scheme, section family or coordinate index is chosen.

`pointIdeal` is its literal native kernel ideal. `pointIdealPullback` is the
original canonical ideal-module comparison attached to the original exceptional
triangle. `pointIdealPullback_inclusion` retains both actual kernel inclusions
and the native pullback-unit comparison. `pointIdeal_comap_le` gives containment
in the original exceptional ideal by the native ideal-sheaf Galois connection.

`pointIdeal_comap_complement` and `exceptionalIdeal_comap_complement` identify
both original ideals with the unit ideal on the literal exceptional complement.
`pointIdealPullback_stalk_isIso_offExceptional` proves that the same canonical
module map is invertible at every original off-E stalk, using the actual ideal
sequences, off-image stalk vanishing and native pullback-stalk comparison.

The original `exceptionalCoordinate` pair is identified with the actual native
chart generators; `exceptionalCoordinate_epi` proves generation of `O_E(1)`.
`firstOrderRestrictionIso` recovers the original first-order restriction
comparison from its actual closed direct image, by full faithfulness.
`firstOrder_lift_pullback` takes the ORIGINAL quotient equation supplied by the
proved cohomological lifts and identifies its actual pulled section with the
same original exceptional coordinate. `firstOrder_lifts_pullback_epi` therefore
proves actual generation of that restricted line by the two original lifts;
it does not assume conormal generation.

The actual first-order ratios lie in the same point ideal. Their original
Cartier products are the original first-order lifts on the selected chart;
monicity of the actual Cartier arrow proves this identity. The whole original
exceptional curve lies in this chart because the selected residue coefficient
is a unit. `pointIdealPullback_pullback_epi` therefore proves generation of the
original pulled canonical map. `pointIdealPullback_epi` uses the native closed
Nakayama theorem, finite stalks of the original Cartier line, and the proved
off-E comparison. Kernel detection gives `pointIdeal_comap_eq`, equality of
the two original ideal sheaves. No structure-sheaf pushforward equality,
normality, regularity, coefficient field or desired conormal-generation premise
is assumed.

`pointChartOpen` is the original selected-coordinate affine open of the same
image. `pointChartHom` evaluates its native coordinate ring at the original
field coefficients; its coefficient and ratio equations retain the original
base map and normalization. `residuePoint_eq_pointChart` applies the actual
field-span chart-comparison theorem, so this is the SAME original point map.
`residueToImage_preimage_pointChart` and `exceptional_preimage_pointChart` prove
that the whole original point and E lie in this original chart. These are
inputs for the actual first-order coordinate ideal sections.

`pointChartCoordinate` is the literal original coordinate ratio restricted to
the selected image chart. Its actual value on the same residue point is
computed by `residueToImage_appLE_pointChartCoordinate`. Thus a zero original
residue coefficient places that coordinate in the ORIGINAL kernel ideal.
`pointChartIdealCoordinate` is the corresponding actual kernel-module section,
with its literal original inclusion equation. `pointChartExceptionalCoordinate`
is its image through the original adjoint ideal comparison; its kernel
inclusion equals the original pulled target coordinate function. These are
actual ideal sections, rather than an assumed ideal-generation datum.

`firstOrderCartierImage_residueCoefficient` derives zero residue directly from
the original Cartier-arrow equation. `pointChartCoordinate_firstOrder_mem`
therefore places each actually retained first-order projective coordinate in
the same original point ideal. Its hypothesis is the literal coordinate
equality already produced by `exists_cartier_firstOrder_projective_presentation`.
No vanishing or ideal-membership witness is assumed for those coordinates.

The internal Cartier multiplier uses the original right unitor, tensor map,
braiding and actual Cartier cancellation to map the original ideal to the
preceding Cartier line. Its composite with the ORIGINAL next Cartier arrow is
the original ideal inclusion followed by the supplied section map. Native
pullback-tensor naturality proves its restriction invertible whenever that
original section restricts invertibly. `pullback_selectedSection_isIso` derives
that property for the original selected section from its actual unit residue
coefficient and the original final restriction isomorphism. No new local
Cartier frame or conormal-generation witness is assumed.

`pointChart_sections_ratio` derives the original local section ratios from the
actual pulled native coordinate maps and their original line-module comparison.
The internal multiplier is invertible on E, so its identity on the two actual
ideal sections converts the original `O_E(1)` basis into generation of the
canonical map, without replacing that map or its adjunction unit.

`exists_cartier_projective_pointIdeal` combines this argument with the proved
cohomological producer for every sufficiently large n. It retains the actual
finite coordinate labeling `ι ≃ Fin (r + 1)`, a commutative Noetherian base,
the original closed projective embedding, the actual Cartier ideal and
restriction comparisons, `IsField k`, and `0 < d`. Its image, original
`Spec k` point, complement inverse and exceptional triangle are the same
ones constructed from the original sections. Formal functions, equality of
the structure-sheaf pushforward, and regularity of the image point are further
obligations beyond this ideal-equality statement.

`pointCartierMultiply`, `pointCartierMultiply_pullback_isIso` and
`pointCartierMultiply_coordinate` expose this same original multiplier and
its proved pair correspondence for the formal-neighborhood comparison. The
last theorem identifies the actual kernel-coordinate product with the
original first-order lift on the original selected chart. Its objects,
coordinate equation and residue-zero equation are the ones already used
in the canonical-map generation proof.

The public multiplier also exposes its necessary data dependencies
`cartierKernelMultiply` and `firstOrderTargetIso`: the same intrinsic tensor
map and the same canonical index-equality isomorphism. Their definitions and
all equations are unchanged. This supplies the module-visible data used by
the actual formal-neighborhood consumer.
