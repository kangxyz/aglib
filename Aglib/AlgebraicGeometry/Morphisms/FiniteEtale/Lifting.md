# Actual cover comparison, sections and deck maps

These focused leaves operate on the original finite-etale schemes and their
actual morphisms. The model application supplies `π : Y ⟶ Spec R`, its section,
the literal residue fibre, the supplied special cover and a point of that cover.
It does not supply a lifted model or source section as an extra input.

| Import suffix | Public role |
| --- | --- |
| `FiniteEtale.Lifting` | Native rank from a displayed base-change comparison and its actual witness point; connectedness of the same forward or chosen inverse cover under a supplied pointwise equivalence. |
| `FiniteEtale.ResidueFiber` | The actual map between the literal residue fibres, its two projection equations, cartesian square, comparison isomorphism, finite/etale and native-rank consequences, and compatibility of the original sections. |
| `FiniteEtale.NonemptyRestriction` | Morphisms from a connected cover are detected on any nonempty actual pullback. The same restriction preserves the exact order of its deck automorphisms. |
| `FiniteEtale.PointComparison` | The original three-arrow point expression through the inverse comparison and pullback projection; lifting it back and applying that same forward comparison recovers the original point. |
| `FiniteEtale.SectionComparison` | The existing `SectionLifting.henselianPointAboveSection` retains the specified residue point under the actual comparison. The universal comparison input remains explicit. |
| `FiniteEtale.DeckLifting` | The same inverse `mapAut`, its counit square, and the literal composite of inverse, restriction and over-base automorphism maps. Its actual covering map and exact order are retained. |
| `FiniteEtale.SourceGeometry` | Native etale stalk regularity and regular-local algebra give normal source stalks; a connected cover of a locally Noetherian regular target is integral. The actual residue fibre is connected under the supplied restriction equivalence. |
| `Finite.GenericSection` | A specified generic point of a finite scheme over an integrally closed domain extends uniquely, with both actual triangles. The finite source need not be integral or connected. |
| `Finite.SectionPullback` | Apply that extension to the literal finite pullback along the supplied section, then project to the same original source. |

The first seven suffixes are under `Aglib.AlgebraicGeometry.Morphisms` and use
`Scheme.FiniteEtale.Lifting` or `Scheme.LocalRing.ResidueFiber`. The final two
are under the same morphism root and use `Scheme.Hom.FiniteSection`.
The ring-level factorization is
`IsIntegrallyClosed.existsUnique_integral_retraction`.

`Spec.ResidueFiber`, owned separately, defines the fibre as the literal
pullback by `Spec.map (.ofHom (IsLocalRing.residue R))`. Its source/target
projections and its section are reused. `ResidueFiber.map_eq_pullbackMap`
compares the induced `Over.pullback.map` with the source's exact three-arrow
`pullback.map`, including the two identity base arrows. `comparisonIso_hom_fst`
and `comparisonIso_hom_snd` retain both projections of the same source fibre.

Rank transport needs the actual comparison isomorphism, a displayed point on
its base, rank at that point, and a preconnected target. Positive rank gives
surjectivity of the same structural map. Deck restriction needs connectedness
of the original lifted covering source and nonemptiness of its actual pullback.
No ambient faithfulness or generic-density hypothesis replaces those premises.

Generic finite-section extension retains `CommRing`, `IsDomain` and
`IsIntegrallyClosed` on the base, a field with the displayed algebra structure
and `IsFractionRing`, and the specified generic map with its original triangle.
There is no DVR or Noetherian restriction. The pullback extension keeps the same
finite source, target section and generic point.

`ProperHenselianComparison R` remains the existing universal theorem-family
input. The conditional adapter applies it to the displayed proper `π`; it
proves no inhabitant of that family. The existing henselian section constructor
also applies the same input at the identity of `Spec R`. A comparison at `Y`
alone is not substituted for that additional use. General point and deck
comparison lemmas need only the pointwise comparison they display.

The unrestricted source `ConnectedPointedFieldScheme` family is not supplied.
For the specific proper smooth generic curves in the source application,
[PointedCurve](../../Geometrically/Connected/PointedCurve.lean) separately proves
`Scheme.geometricallyConnected_of_pointed_proper_smooth_curve`. It keeps the
same structural map, actual rational point and section triangle, and requires
smooth relative dimension one, properness, Noetherianity and connectedness of
that same scheme. The original generic source supplies these guards. The nine
leaves above do not import this separate provider. Explicit cycle/polygon constructors,
marked isogenies, `Incoming`, `ActualLocalModel`, `CurveModel` and
`ModelGeometry` assembly endpoints remain downstream. Actual Picard/Hilbert
representability and Zariski–Nagata purity are outside this migration scope.

Source selection: the ten modules
`R5Lab.AlgebraicGeometry.Curves.LocalModels.CyclicCovers.{DeckLifting,GeneralLift,Henselian,MarkedCycles,MarkedPolygons,OneGonLift,OneGonOrigin,Origin,Polygon,SourceModel}`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, plus the exact allocated
`R5Lab.Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.NonemptyRestriction:28–68`
and `Morphisms.Finite.GenericSection:25–130` prerequisites. Their public generic
operations are migrated or reused as above; application specializations retain
their original premises and maps.
