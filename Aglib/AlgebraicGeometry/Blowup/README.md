# Universal blowups and saturated affine charts

[UniversalProperty](UniversalProperty.lean), in `Scheme.Blowup`, uses the existing
`Localization.Away.saturatedChart A I a` as the literal algebra A[I/a] inside
A[1/a]. Denominator torsion is killed; a polynomial quotient is not substituted.
`cartierPullback I f` means local rank one of the actual image ideal module of
`I.comap f`. Its equivalence with the native `Scheme.Hom.IsEffectiveCartier`
predicate on that actual closed subscheme is proved directly. The module and
its inclusion are the existing `Scheme.Hom.idealModule` and canonical maps.

`BlowupDatum I` consists of a scheme, its structure map, Cartierness and the
final-object universal property for the actual inverse-image ideal. Unique
lifts, comparison isomorphisms and isomorphisms away from the centre use these
same objects and maps.

[AffineConstruction](AffineConstruction.lean) constructs the original Rees Proj
over an arbitrary commutative ring, its saturated charts, and Cartierness of
the actual inverse-image centre. Its blowdown is proper over a Noetherian ring.
[AffineLiftingCover](AffineLiftingCover.md) produces affine pivot neighborhoods
from a Cartier image ideal on an arbitrary test scheme.
[AffineUniversalProperty](AffineUniversalProperty.md) then proves the full
universal property of that same Proj and constructs `affineProjBlowupDatum`.
Neither the affine construction nor its universal property needs a domain,
reducedness, finite generation or Noetherianity.

[FlatBaseChange](FlatBaseChange.md) supplies the exact `BlowupFlatBaseChange`
family. For a flat map and given universal blowups, the pre-existing canonical
comparison map is cartesian. The constructed datum uses the literal pullback;
its comparison isomorphism has both original projection equations. The lower
[Cartier comap theorem](../IdealSheaf/Cartier/FlatComap.lean) proves local rank
one of the actual inverse-image ideal under arbitrary flat morphisms.

[Construction](Construction.md) glues the actual affine datums by their canonical
open maps and constructs `blowupDatum I` for every scheme and ideal sheaf. The
constructed datum has the full universal property on arbitrary test schemes.
Its `noetherianBlowupExistence` corollary supplies the original retained family.
[Properness](Properness.md) proves `noetherianBlowupProper` for every given
universal representative over a locally Noetherian base, using target locality
and its actual affine pullbacks. [AffineAtlas](AffineAtlas.md) proves
`blowupAffineAtlas` with the original saturated chart rings and projection maps.
All four retained theorem-family interfaces therefore have proved suppliers.

[AffineCenter](AffineCenter.lean) identifies the actual kernel centre of a
surjective ring map. [BaseChange](BaseChange.lean), in `Scheme.Blowup.BaseChange`,
constructs the canonical map for an equality of actual centre ideals and proves
its identity/composition laws. Its parameterized cartesianness interface accepts
the proved `blowupFlatBaseChange` supplier. Its flat and etale corollaries concern
the comparison map, and its
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

[RegularPoint](RegularPoint.md) identifies the literal closed-point fibre of
the actual maximal-ideal blowup of a two-dimensional regular local ring with
the native projective line over its original residue field. Its
[parameter charts](RegularPoint/Charts.md) and inverse-image-centre comparison
preserve the original projections. The isomorphism uses one chosen ordered
regular pair. [Regularity](RegularPoint/Regularity.md) proves regularity of
every actual stalk of this constructed blowup from the same regular-local
dimension-two hypotheses. It uses the literal parameter charts, their regular
principal fibre quotients and the actual stalk maps.
[Scheme](RegularPoint/Scheme.md) extends this result to the actual blowup
of a closed point on any scheme with regular stalks when its original
stalk has dimension two. The canonical comparison with the local-ring blowup
preserves both projections and uses the original centre ideal and stalk maps.
Normal-line comparison and contraction remain separate obligations.
