# Topological section, support and filtered-colimit interfaces

These leaves extend `TopCat.Sheaf` on actual topological sheaves and opens. They contain no scheme-specialized cohomological-dimension conclusion.

| Focused import | Main result/interface and exact boundary |
| --- | --- |
| `Aglib.Topology.Sheaves.BasisExactness` | Actual abelian-group sheaf exactness, acyclicity and quasi-isomorphism detection on a specified `Opens.IsBasis`, with original sectionwise premises. |
| `Aglib.Topology.Sheaves.MayerVietorisSections` | Actual section-complex Mayer–Vietoris exactness. Short exactness needs flasque terms and stated `HasSheafify`; the upper-bound result keeps bounds `n` on opens and `n-1` on their intersection. |
| `Aglib.Topology.Sheaves.FreeAbelianPullback` | The native sheafified free abelian representable on an open commutes with actual inverse image, naturally in the open. The Hom comparison retains the original pullback adjunction and represented section equivalence; there is no scheme or quasicoherence hypothesis. |
| `Aglib.Topology.Sheaves.FilteredColimits` | In a Noetherian space, filtered pointwise additive colimits are sheaves and are computed on every open. Shape is a universe-`u` small filtered category, coefficients `AddCommGrpCat.{u}`. |
| `Aglib.Topology.Sheaves.ClosedSupport` | A closed embedding and actual zero stalks off its image give `closedSupportIso` and `closedSupportCohomologyEquiv` with the actual pullback/direct-image maps. No Noetherian hypothesis is required. |
| `Aglib.Topology.Sheaves.Godement` | The functorial stalk–skyscraper product gives a monomorphic unit and flasque target; `godementDiagramSequence_shortExact` is the actual associated diagram sequence. This is the flasque support construction, not the scheme dimension endpoint. |
| `Aglib.Topology.Sheaves.SupportedAway` | Actual open-intersection sheaves, supported-away kernels and neighborhood diagrams. The colimit comparison retains its section/stalk-zero and shape hypotheses. |

[FilteredColimits](FilteredColimits.lean), [ClosedSupport](ClosedSupport.lean), [Godement](Godement.lean) and [SupportedAway](SupportedAway.lean) are distinct cuts of the former mixed source. Exact coefficient, compactness/Noetherian and universe conditions belong to the particular result, not the former filename.

Consumers are [scheme injective/affine/finite-support/Noetherian comparison](../../AlgebraicGeometry/Cohomology/README.md), actual module local detection and two-open cohomology. Generic Cech combinatorics is below schemes in [site Cech](../../CategoryTheory/Sites/SheafCohomology/Cech/README.md); generic closed-subspace dimension is in [Topology/KrullDimension](../KrullDimension/README.md).

[FreeAbelianPullback/Composition](FreeAbelianPullback/Composition.lean)
constructs `abelianPullbackCompIso` from the original native inverse-image
adjunctions and their literal direct-image composition. Its Hom normalization
retains the original units. `openFreeAbelianPullbackIso_comp_hom` and
`_comp_inv` prove that successive original free-open comparisons give this
same composite comparison on the actual inverse-image opens. These are pure
topological sheaf statements, with no scheme or cohomology hypothesis.

# Exact open extension by zero

[ExtensionByZero](ExtensionByZero.lean) constructs
`TopCat.Sheaf.extensionByZero U`, the native left adjoint to restriction of
abelian sheaves to an open subspace, and proves that it is exact. The original
construction is opposite Kan extension along the inclusion of opens followed
by sheafification. The [lower Kan lemma](../../CategoryTheory/Functor/KanExtension/ClosedImage.lean)
proves the needed preservation of monomorphisms; no scheme, compactness or
quasicoherence premise is used.

[ExtensionByZero/Free](ExtensionByZero/Free.lean) identifies extension by zero
of the original free abelian sheaf on an open with that on its ambient image.
The natural isomorphism and its represented-section formulas retain the
original adjunction unit and coefficient maps. This is the input to the
native Ext comparison under open restriction.

[Restriction](Restriction.lean) gives the actual sectionwise restriction /
geometric direct-image adjunction. `openRestrictionPullbackIso` uses native
uniqueness of left adjoints, and its unit and Hom-equivalence formulas retain
the original presheaf restrictions. It is the normalized comparison used to
identify the extension-by-zero cohomology map with geometric inverse image.

[Cohomology/Restriction](Cohomology/Restriction.lean) proves
`cohomologyOpenRestrictionAddEquiv`: the original ambient `Sheaf.H'` on an
image open equals the original `Sheaf.H'` of the actual restricted sheaf.
Its forward formula is the original exact Ext map preceded by the native
extension-by-zero adjunction unit. Coefficient naturality is proved, with no
acyclicity or scheme hypothesis. The
[scheme restriction comparison](../../AlgebraicGeometry/Cohomology/Restriction/README.md)
uses it with the existing whole-space `Sheaf.H` comparison.

[Cohomology/Restriction/Geometric](Cohomology/Restriction/Geometric.lean)
identifies that exact Ext equivalence with original geometric inverse image.
`openFreeAbelianRestriction_unit_geometric` identifies the original free-open
unit with the native free-open pullback map, and
`cohomologyOpenRestrictionAddEquiv_geometric` proves the equality in every
degree. Its typed inverse-image aliases delegate to the same native functor
and comparison; they expose the underlying site-sheaf categories for Ext
instance inference.
