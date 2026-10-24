# Finite arc iteration on the original point blowups

The focused import is `Aglib.AlgebraicGeometry.Blowup.Arc.Iteration`.
It supplies the local arc termination step in the general
surface-resolution argument. It uses the actual one-step `Blowup.Arc` provider,
the actual local-ring descent in `ArcTermination.Descent`, and canonical flat
base change for ordinary blowups. It does not use a chain interface requiring
regular centres.

The initial surface hypotheses are a Noetherian local two-dimensional domain
`C`, the original surjection `f : C → R` onto a DVR `R`, a chosen element `t`
mapping to a uniformizer, and regularity of the original localization at
`ker f`. The algebraic provider derives the generic DVR and constructs
`LocalArcState.ofRegularGenericSurface`. Its actual `iterate` supplies the
literal rings, quotient maps to the same `R`, exceptional parameters, and
scalar maps used throughout this module.

## Realization and the actual successor

`Realization S` records an actual locally Noetherian scheme `X` and a flat
preimmersion `localMap : Spec S.Ring → X`. The original quotient arc
`Spec S.quotient ≫ localMap` is a closed immersion. These are induction
invariants: `initial` constructs them for the original source spectrum,
and `Realization.next` derives them for the constructed next blowup.
Neither a geometric successor nor a desired terminating chain is an input.

`Realization.point` is the image of the actual local ring's closed point.
`arc_closedPoint` identifies it with the image of the original DVR closed
point. Since the arc is closed, `point_isClosed` proves that this is an actual
closed point of the original scheme.

`isIso_stalkClosedPointTo` derives the actual scheme-stalk isomorphism from
flatness and surjectivity on stalks. The native local-spectrum factorization
then proves `pointCentre_comap`: the actual residue-field point-centre ideal
pulls back to the actual maximal-ideal centre on `Spec S.Ring`. The auxiliary
point-centre theorem imported from `RegularPoint.Scheme` has no regularity
hypothesis. No centre compatibility or stalk isomorphism is supplied as an
extra premise.

`Realization.nextBlowup` is `blowupDatum` of this actual closed point's ideal.
`comparison` is its canonical comparison with `Arc.pointBlowup S.Ring`, using
the proved centre equality. `comparison_isPullback` is the actual flat blowup
base-change square. Hence the comparison is flat and a preimmersion.

The source of `Realization.nextMap` is literally `Spec S.next.Ring`, where
`S.next.Ring` is the original `arcLocalRing`. Its map is the composite of the
original prime-localization map, the original saturated chart, and the
canonical flat comparison. Each factor is flat and a preimmersion. Thus the
next local ring is realized without choosing an arbitrary isomorphic ring
or transporting the descent measure across ring isomorphisms.

The original atlas and comparison triangles give `nextMap_scalar`. Together
with the original quotient equation this proves `nextArc_map`. The actual
inverse-image point ideal on the original DVR is Cartier, by the proved centre
pullback and `Arc.cartier_specMap`. Universal uniqueness gives
`next_arc_eq_lift`: the constructed next arc is the original universal lift.
The actual point blowdown is proper, hence separated and locally of finite
type. It preserves local Noetherianity, and `IsClosedImmersion.of_comp` proves
that the next actual arc remains closed. This closes all successor invariants
without a regular-centre hypothesis.

## Original maps, selected points, and termination

`stalk_quotient_comp` and `stalk_scalar_of_triangle` derive the canonical
quotient and scalar equations using the native local-spectrum equivalence.
Their equations retain the explicit source-point stalk transport.
`compositeStalkMap` is the original blowdown stalk map with its actual
composite-image source fixed. `Realization.stalkIso_quotient` and
`stalkIso_scalar` specialize these equations to the constructed realization.
All quotient maps still target the same original `R`.
`pointStalkIso` retains the actual equality of scheme points in those
transports. `Realization.localStalkMap` is the original local-spectrum stalk
map with this selected source fixed, and `stalkIso_hom` gives its literal
value as the isomorphism's forward arrow. `nextChartBase` similarly retains
the original localization arrow with the literal next-state target fixed.
The original factorization and scalar triangles are composed over fixed
native objects before specializing the dependent iterate carriers.

`Realization.iterate` is dependent on the already constructed
`LocalArcState.iterate`: its ring at every stage is the literal algebraic
iterate. `blowdown` is the actual ordinary point blowdown at the preceding
selected point. `iterate_arc_map`, `iterate_map_point`, and
`iterate_scalar_map` retain the original arc, point, and scalar triangles.
`originMap` composes these original scheme blowdowns. The corresponding
equations preserve both the original arc and the original coefficient map.
`iterateScalarArrow_quotient` and `iterateScalarArrow_parameter` retain the
original surjection and chosen parameter under the exact scalar composite.

`Realization.exists_regular_iterate` applies the proved finite algebraic
termination theorem, whose successor decrease is proved for the actual
kernel-generator count and least realized relation exponent. At its finite
regular ring iterate, the derived stalk isomorphism proves regularity at the
same selected point on the original scheme iterate.
`exists_regular_point_iterate_of_regular_surface` starts this construction
from the original surface hypotheses above. No dimension or regularity
condition is imposed on a successor.

This is local arc termination. It does not construct a suitable surjective
DVR arc for an arbitrary singularity, classify rational double points, or
assert a global resolution theorem. A singularity consumer must supply the
original surjection, uniformizer lift, and regularity at its actual kernel.

The fixed mathematical basis is Section 7 D4, lines 223–235, of the resolution
report, SHA-256
`d1368ff17ca40798ccc1de88fcd84efa0df1bed318799880db0d7fe75d678da9`, and
[Stacks, Tag 0BG3](https://stacks.math.columbia.edu/tag/0BG3). The coefficient
ring is the original source, the quotient DVR remains the original `R`, and
each normalized relation retains its own exponent. No persistent cubic chart
shape or RDP classification is imported.
