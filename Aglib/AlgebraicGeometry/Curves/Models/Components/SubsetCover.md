# SubsetCover

Native module: `Aglib.AlgebraicGeometry.Curves.Models.Components.SubsetCover`.

Same C,i and literal component index; native FiniteClosedCover.unionIdeal is exactly the finite kernel intersection. Finset.map e.toEmbedding is the precise reindexing; actual partial-overlap two-point iso discharges reducedness, and exact pairwise morphism compatibility supplies finite descent to any T. No ideal-intersection/base-change distribution is assumed.

Source: `R5Lab.AlgebraicGeometry.Curves.LocalModels.Incidence.FiniteClosedCover`, R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Ranges: `[[47, 242], [275, 372]]`. SHA-256 `e8b461f107b1c6de51707df54615d8bbdf439d26277385d9f8e9312155c1d84c`.

| Source declaration | Native declaration or exact reuse |
| --- | --- |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.SplitRationalComponents.subsetIdeal` | `AlgebraicGeometry.Scheme.FiniteClosedCover.unionIdeal i S (definitionally the same kernel intersection)` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.SplitRationalComponents.subsetScheme` | `AlgebraicGeometry.Scheme.FiniteClosedCover.unionScheme i S` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.SplitRationalComponents.subsetMap` | `AlgebraicGeometry.Scheme.FiniteClosedCover.unionMap i S` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.SplitRationalComponents.subsetIdeal_radical` | `AlgebraicGeometry.Scheme.FiniteClosedCover.unionIdeal_radical i S` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.SplitRationalComponents.subsetScheme_reduced` | `AlgebraicGeometry.Scheme.FiniteClosedCover.unionScheme_reduced i S` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.SplitRationalComponents.subsetSupport` | `AlgebraicGeometry.Scheme.FiniteClosedCover.unionSupport i S; replace each Set.range (i w) by w.val using hrange, the source finite supremum is the same finite closed union` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.SplitRationalComponents.subsetIdeal_eq_vanishingIdeal` | `AlgebraicGeometry.Scheme.FiniteClosedCover.unionIdeal_eq_vanishingIdeal i S, with the preceding exact support identification under hrange` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.SplitRationalComponents.subsetMap_range` | `AlgebraicGeometry.Scheme.FiniteClosedCover.unionMap_range i S, rewritten by hrange` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.SplitRationalComponents.subsetScheme_empty` | `AlgebraicGeometry.Scheme.FiniteClosedCover.unionScheme_empty i` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.SplitRationalComponents.otherIdeal_le_subsetIdeal` | `AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily.otherIdeal_le_subsetIdeal` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.SplitRationalComponents.subsetToOther` | `AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily.subsetToOther` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.SplitRationalComponents.subsetToOther_closed` | `AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily.subsetToOther_closed` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.SplitRationalComponents.subsetIntersection` | `AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily.subsetIntersection` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.SplitRationalComponents.subsetIntersectionToOther` | `AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily.subsetIntersectionToOther` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.SplitRationalComponents.subsetIntersectionToOther_closed` | `AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily.subsetIntersectionToOther_closed` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.SplitRationalComponents.subsetIntersectionToTwoPoints` | `AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily.subsetIntersectionToTwoPoints` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.SplitRationalComponents.subsetIntersection_reduced` | `AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily.subsetIntersection_reduced` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.genericUnionIdeal_eq_native` | `rfl: FiniteClosedCover.unionIdeal i S = the source finite kernel intersection` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.genericUnionMap_eq_native` | `rfl: FiniteClosedCover.unionMap i S = the subscheme inclusion of that same ideal` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.genericPartialOverlap_reduced` | `AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily.subsetIntersection_reduced π i S a ha e` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.reindexedUnionIdeal_eq_native` | `AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily.reindexedUnionIdeal_eq_native` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.reindexedUnionIso` | `AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily.reindexedUnionIso` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.reindexedPartialOverlap_reduced` | `AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily.reindexedPartialOverlap_reduced` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.reindexedPartialOverlap_family` | `AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily.reindexedPartialOverlap_family` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.reindexed_components_cover` | `AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily.reindexed_components_cover` |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.GeometricMinimality.nativeReindexedDesc` | `AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily.nativeReindexedDesc` |

Compilation scope and actual cold imports are recorded in the author handoff. Source correspondence supplies no model-existence, representability, purity, independent review or adoption verdict.
