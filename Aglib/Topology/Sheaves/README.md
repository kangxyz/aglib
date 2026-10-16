# Topological section, support and filtered-colimit interfaces

The sheaf leaves extend `TopCat.Sheaf` on actual topological sheaves and opens.
The [Cech family](Cech/README.md) additionally works with actual presheaves on
`Opens X`, without imposing a sheaf condition. These leaves contain no
scheme-specialized cohomological-dimension conclusion.

| Focused import | Main result/interface and exact boundary |
| --- | --- |
| `Aglib.Topology.Sheaves.BasisExactness` | Actual abelian-group sheaf exactness, acyclicity and quasi-isomorphism detection on a specified `Opens.IsBasis`, with original sectionwise premises. |
| `Aglib.Topology.Sheaves.MayerVietorisSections` | Actual section-complex Mayer–Vietoris exactness. Short exactness needs flasque terms and stated `HasSheafify`; the upper-bound result keeps bounds `n` on opens and `n-1` on their intersection. |
| `Aglib.Topology.Sheaves.FilteredColimits` | In a Noetherian space, filtered pointwise additive colimits are sheaves and are computed on every open. Shape is a universe-`u` small filtered category, coefficients `AddCommGrpCat.{u}`. |
| `Aglib.Topology.Sheaves.ClosedSupport` | A closed embedding and actual zero stalks off its image give `closedSupportIso` and `closedSupportCohomologyEquiv` with the actual pullback/direct-image maps. No Noetherian hypothesis is required. |
| `Aglib.Topology.Sheaves.Godement` | The functorial stalk–skyscraper product gives a monomorphic unit and flasque target; `godementDiagramSequence_shortExact` is the actual associated diagram sequence. This is the flasque support construction, not the scheme dimension endpoint. |
| `Aglib.Topology.Sheaves.SupportedAway` | Actual open-intersection sheaves, supported-away kernels and neighborhood diagrams. The colimit comparison retains its section/stalk-zero and shape hypotheses. |
| `Aglib.Topology.Sheaves.Cech.Restriction` | Actual open-intersection presheaf restriction, restricted Cech exactness and original cosimplicial comparison, with the stated coefficient/product hypotheses. |
| `Aglib.Topology.Sheaves.Cech.Cocycles` | Literal module-presheaf cocycle/coboundary equations from the supplied degree-one exactness; no sheaf or covering condition is added. |

[FilteredColimits](FilteredColimits.lean), [ClosedSupport](ClosedSupport.lean), [Godement](Godement.lean) and [SupportedAway](SupportedAway.lean) are distinct cuts of the former mixed source. Exact coefficient, compactness/Noetherian and universe conditions belong to the particular result, not the former filename.

Consumers are [scheme injective/affine/finite-support/Noetherian comparison](../../AlgebraicGeometry/Cohomology/README.md), actual module local detection and two-open cohomology. Generic Cech combinatorics remains in [site Cech](../../CategoryTheory/Sites/SheafCohomology/Cech/README.md), and actual open/presheaf specializations are in [topological Cech](Cech/README.md); generic closed-subspace dimension is in [Topology/KrullDimension](../KrullDimension/README.md).
