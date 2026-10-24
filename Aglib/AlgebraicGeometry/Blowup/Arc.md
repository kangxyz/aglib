# One closed arc step on the original point blowup

The focused import is `Aglib.AlgebraicGeometry.Blowup.Arc`. It supplies the
one-step construction for [finite arc iteration](Arc/Iteration.md), using
the actual saturated chart, localization, universal blowup atlas and
properness interfaces. No regular-centre blowup-chain interface is used.

For a local ring `C`, `pointBlowup C` is the actual universal blowup of the
ideal sheaf cut out by `C → C / m_C`. Let the original map `f : C → R` be
surjective onto the same DVR `R`, and let `t` map to a uniformizer. `center_eq`
uses these actual hypotheses to prove `arcCenterIdeal f t = m_C`.
The native chart comes directly from the maximal-ideal atlas of the original
universal representative `B`. `chartIdealEquiv` transports its ring along the
proved equality of centre ideals as a `C`-algebra equivalence. Thus `chart`
has the literal ring `arcChart f t` while the scheme and blowdown remain
literally those of `B`; its original scalar-map triangle is proved using the
algebra equivalence's coefficient equation.

`closedArcChartData` constructs the actual lift, its original-arrow value,
the point, stalk comparison, coefficient arrow, and quotient/parameter
and conditional closedness equations together over abstract native objects.
`stepData` specializes this single witness to the original rings and blowup.
The public lift, point, stalk, coefficient and all equations project this same
witness. The stalk arrows use one explicitly typed source at the image of the
original closed point throughout the generic quotient and coefficient pastes.
`localScalar` and `localQuotient` are the original `arcLocalBase` and
`arcLocalMap` with their native localization endpoints fixed before this
specialization. `lift_value` identifies the arrow with `Spec (arcMap)` followed by the
original chart, and `lift_map` retains its base triangle with the original
surjection. The actual inverse-image
centre is `(f(t))`; multiplication by the nonzero `f(t)` proves this ideal is
free of rank one. Thus `cartier_specMap` proves the Cartier condition directly
on the actual image ideal, and `lift_eq_universalLift` identifies the explicit
chart lift with the actual universal lift. This uses no identification of
blowups under the nonflat quotient map.

`chartPoint` is the prime obtained by pulling the original DVR maximal ideal
back through the original chart quotient. `point` is its image on the original
blowup, and `lift_closedPoint` identifies it with the lifted arc's closed
point. `point_chart` retains its value on the original chart, and `map_point`
proves that it lies over the original closed point of `Spec C`.

`stalkIso` and `stalkEquiv` compare this actual original-scheme stalk with the
already defined `arcLocalRing`. An explicit identity ring equivalence keeps
the affine stalk's native prime-localization presentation and the original
`arcLocalRing` presentation separate until their comparison is composed.
The native atlas chart and its immersion/triangle equations are retained in
one shared witness. Scheme points and top-open membership proofs retain
their native carriers. `stalkIso_quotient` identifies the original
stalk quotient to the same `R` with `arcLocalMap`; the proof uses localization
uniqueness after the canonical affine-stalk isomorphism. `coefficient` is the
original map from `C` to the scheme stalk, formed from the blowdown's original
global-section map and germ. `coefficient_stalkIso` identifies it with
`arcLocalBase`. The quotient and distinguished-parameter equations retain the
original surjection and chosen element, not merely their residue classes.

When `C` is Noetherian, the original point blowdown is proper and hence
separated. Since the original quotient arc is a closed immersion, native
closed-immersion descent along this separated blowdown proves
`lift_isClosedImmersion`. Therefore `point_isClosed` gives an actual closed
next centre on the original scheme. `exists_closedLift` specializes these
constructions to the actual `pointBlowup C`.

No regularity of `C`, its original closed point, or the new stalk is assumed.
This module is one geometric step. [Iteration](Arc/Iteration.md) realizes the
algebraic iterates on successive ordinary point blowups by flat
preimmersions and obtains a regular selected stalk. Its initial surjection,
uniformizer lift and generic-regularity hypotheses remain explicit.
Neither module constructs such an arc for an arbitrary singularity or
asserts a general resolution theorem.

The proof basis is Section 7 D4, lines 223–235, of the frozen resolution report,
SHA-256 `d1368ff17ca40798ccc1de88fcd84efa0df1bed318799880db0d7fe75d678da9`,
and [Stacks, Tag 0BG3](https://stacks.math.columbia.edu/tag/0BG3), with the
original source coefficient ring and original quotient DVR retained.
