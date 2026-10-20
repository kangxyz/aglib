# Blowup data, actual saturated charts and conditional geometric interfaces

[UniversalProperty](UniversalProperty.lean), in `Scheme.Blowup`, uses the existing
`Localization.Away.saturatedChart A I a` as the literal algebra A[I/a] inside
A[1/a]. Denominator torsion is killed; a polynomial quotient is not substituted.
`cartierPullback I f` means local rank one of the actual image ideal module of
`I.comap f`. Its equivalence with the native `Scheme.Hom.IsEffectiveCartier`
predicate on that actual closed subscheme is proved directly. The module and
its inclusion are the existing `Scheme.Hom.idealModule` and canonical maps.

`BlowupDatum I` supplies a scheme, its structure map, Cartierness and the actual
final-object universal property. Unique lifts, comparison isomorphisms,
properness transfer and isomorphisms away from the centre are proved from those
inputs. These consequences do not construct a blowup. The four families
`NoetherianBlowupExistence`, `NoetherianBlowupProper`, `BlowupFlatBaseChange` and
`BlowupAffineAtlas` remain explicit unsupplied propositions. Their original
local-Noetherian, Noetherian-ring and actual-flat-map hypotheses are retained.

[AffineCenter](AffineCenter.lean) identifies the actual kernel centre of a
surjective ring map. [BaseChange](BaseChange.lean), in `Scheme.Blowup.BaseChange`,
constructs the canonical map for an equality of actual centre ideals and proves
its identity/composition laws. Cartesianness uses the explicit flat-base-change
family. Its flat and etale corollaries concern the comparison map, and its
properness corollary retains properness of the original blowdown. No arbitrary
nonflat base-change theorem or universal flatness of a blowdown is asserted.

[CoordinateOverlap](CoordinateOverlap.lean) transports literal affine atlas
charts along specified ring equivalences, with actual localization overlaps and
projection triangles. [GeneratorAtlas](GeneratorAtlas.lean) derives generator
coverage from the supplied atlas. [UnitLocus](UnitLocus.lean) and
[BasicOpenIsomorphism](BasicOpenIsomorphism.lean) identify the actual unit locus
and the corresponding blowdown restrictions. [RegularAway](RegularAway.lean)
transports actual stalk regularity from the complement of an actual closed centre.

The independent lower [power-node algebra](../../RingTheory/Blowup/PowerNode/README.md)
computes actual saturated chart rings and transition maps. It does not supply
these global geometric families or an actual node-resolution scheme.
