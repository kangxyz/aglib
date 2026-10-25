# Original cohomology presheaves and higher-image stalks

This family retains the original small-etale cohomology, chart pullbacks and
native higher direct images for `AbelianSheaf.{u,u+1}`. Group resizing
changes the cohomology carriers, not the coefficient sheaf or higher-image
object.

| Source | Canonical interface |
| --- | --- |
| [OriginalPresheaf](OriginalPresheaf.lean) | The original represented-cohomology presheaf, its size-correct version, actual resolution comparison and sheafification to `higherDirectImage`. |
| [ChartRestrictionNaturality](ChartRestrictionNaturality.lean) | Every chart restriction agrees with original scheme cohomology pullback and its commuting-triangle coefficient transport in all degrees. Base, chart and slice Ext universes are retained. |
| [FibreProductPresheaf](FibreProductPresheaf.lean), [FibreProductStalk](FibreProductStalk.lean) | Original cohomology of the literal fibre products, original restrictions and canonical maps from original classes to higher-image germs. |
| [GeometricOriginalDiagram](GeometricOriginalDiagram.lean) | The actual compatible-system cohomology diagram agrees with the original, unresized scheme-H diagram before resizing. |
| [ResizeCohomologyDiagram](ResizeCohomologyDiagram.lean), [ResizeCohomologyReindex](ResizeCohomologyReindex.lean) | Whole-diagram and reindexing comparisons retain the actual coefficient maps and explicit size/Ext/colimit premises. |
| [EtaleDirectImageMate](EtaleDirectImageMate.lean) | For arbitrary vertical `f` and étale horizontal `g`, the original ordinary exchange is the actual chart isomorphism, with original unit/counit normalization. |
| [BaseChangeChartRelative](BaseChangeChartRelative.lean) | Whole `TwoSquare` interchange of the four original higher exchanges retains both inverse-image square comparisons and eight independent derived models. Its original component formula remains available without Cartesian or invertibility assumptions. |
| [BaseChangeSectionComparison](BaseChangeSectionComparison.lean) | The original whole unit and relative-exchange equations give the actual section square before coefficient evaluation. Its component view retains the original section pullback and inverse coefficient comparison. This supplies an input to neighborhood-germ comparison, not proper base change by itself. |
| [ChartExchangeMaps](ChartExchangeMaps.lean) | The chart witness uses the shared whole comparison family. Its original-factor, family-value and `IsIso` views preserve the four arbitrary models and obtain invertibility from the original etale exchange. |

## Geometric neighborhood colimit

[GeometricCohomologyStalk](GeometricCohomologyStalk.lean) defines
`geometricCohomologyStalkIso`. Let `R,Ω : Type u`, with `R`
commutative, `Ω` a separably closed field and `Algebra R Ω`.
For `f : X ⟶ Spec R`, actual `F : AbelianSheaf.{u,u+1} X` and
every natural `q`, the colimit over the actual
`GeometricEtaleNeighborhood R Ω` of the size-correct original fibre-product
cohomology diagram is isomorphic to the original geometric stalk of
`(higherDirectImage f q).obj F`.

The theorem retains `HasExt.{w}` on `X`, `HasExt.{s}` on the
displayed slice categories and `HasExt.{e}` on each literal fibre product.
No qcqs or finite-type premise on `f` is added. The normalization
`ι_geometricCohomologyStalkIso_apply` sends each original class, through
its explicit `Shrink` comparison and colimit injection, to its literal
original higher-image germ.

The [geometric neighborhood family](../Finite/GeometricNeighborhoodStalk.lean)
supplies the actual final functor to the original point index and the germ
formula. The [original inverse-image stalk comparison](../GeometricPoints/InverseImage/README.md)
remains in its own geometric-point owner.

## Marked strict-local cohomology comparison

[ChartStrictLocalComparison](ChartStrictLocalComparison.lean) defines
`chartStrictLocalCohomologyAddEquiv`. For a qcqs map `f`, the original
higher-image stalk at a marked separably closed geometric point is additively
equivalent to original `Sheaf.H` on its literal strict-local base change,
in every natural degree. [ChartLimitContinuity](ChartLimitContinuity.lean)
applies the genuine [scheme-limit continuity theorem](../Continuity/SchemeLimit.lean);
no section-colimit or cohomological-continuity certificate remains an input.

The base scheme is arbitrary. The construction retains a chosen affine etale
monomorphism chart through the point, independent base/slice/stage/limit Ext
universes, and the stated group-colimit existence. An affine open chart
through the actual field-valued point exists. The apex is literally
`Spec (GeometricEtaleColimit R Ω)` and its base change is a single original
fibre product. The ring is local and henselian with separably closed residue.
Its actual residue map to Ω is retained; the residue need not equal Ω.
No separate identification with a differently named strict henselization is
asserted.

| Source | Original-map conclusion |
| --- | --- |
| [PointedNeighborhoodLimit](PointedNeighborhoodLimit.lean), [PointedNeighborhoodBaseChange](PointedNeighborhoodBaseChange.lean) | Actual limiting cones over all original pointed neighborhoods, with original structure and marked field-point equations. |
| [ChartPointedComparison](ChartPointedComparison.lean) | `chartStrictLocalCohomologyAddEquiv_pointedGerm` sends every original pointed-neighborhood germ to its actual limit-leg cohomological transfer, including neighborhoods outside the chosen chart. |
| [ChartStrictLocalNaturality](ChartStrictLocalNaturality.lean) | The final equivalence commutes with original coefficient morphisms and their inverse-image cohomology maps. |
| [ChartStrictLocalZero](ChartStrictLocalZero.lean) | The original ordinary direct-image germ, followed by the native derived-zero unit and final equivalence, is original `pullbackSectionsMap` after `Sheaf.H.equiv₀`. |

The lower [germ naturality](FibreProductGermNaturality.lean),
[germ restriction](FibreProductGermRestriction.lean) and
[degree-zero germ](FibreProductGermZero.lean) retain the original resolution,
sheafification and point maps. The final comparison is consequently more
than an isomorphism of endpoints. It does not itself assert general proper
base change or an unbounded derived theorem.

## Original global classes and the actual exchange

[GlobalSections](GlobalSections.lean) constructs the original
`cohomologyToHigherSections`. [BaseChangeGlobalSections](BaseChangeGlobalSections.lean)
identifies the actual higher exchange on this map with original cohomology
pullback for any commuting square, all natural degrees, two independent Ext
universes and four independent derived models.
[BaseChangeGlobalGerms](BaseChangeGlobalGerms.lean) retains the original
stalk-unit and global-class germ. [GlobalSectionsField](GlobalSectionsField.lean)
proves bijectivity of the same edge over a separably closed target field.
No general-base edge injectivity, properness or PBC premise is asserted.

[ChartCycleWitness](ChartCycleWitness.lean), [ChartTargetCycles](ChartTargetCycles.lean)
and the generic actual-resolution comparison supply neighborhood-cycle inputs.
[BaseChangeNeighborhoodGerms](BaseChangeNeighborhoodGerms.lean) exports the
actual all-degree section and arbitrary-pointed-neighborhood germ equations.
[GeometricComparisonExchange](GeometricComparisonExchange.lean) compares the
original stalk exchange with the two cohomology transfers over one common
geometric point. [GeometricStalkExchange](GeometricStalkExchange.lean) obtains
invertibility from the stated bijectivity hypotheses on the actual local
transfers, retaining the projected Ext dictionaries and original maps. The
[proper family](../Proper/README.md) supplies those transfers on its selected
route to locally torsion higher and D+ proper exchange. Unbounded exchange
retains its separate homological obligations.
[ChartLimitZero](ChartLimitZero.lean) separately spreads original vanishing
on an actual qcqs affine-transition limit to a genuine pointed etale stage.
