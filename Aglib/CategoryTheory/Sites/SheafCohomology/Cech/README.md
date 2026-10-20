# Generic Cech resolutions, exactness and coefficient comparison


[CoverResolution](CoverResolution.lean), imported as
`Aglib.CategoryTheory.Sites.SheafCohomology.Cech.CoverResolution`, constructs
`CategoryTheory.Presheaf.Cech.resolution` from a map of set-valued presheaves:
the degree `-n` term is the sheafification of the free abelian presheaf on
ordered `(n + 1)`-tuples of lifts with their original target section. It requires
no limits in the site category. The pointwise-image augmentation is a
quasi-isomorphism for every presheaf map. For locally surjective maps in the
stated `Type (max u v)` universe, `resolutionAugmentation_quasiIso` proves the
augmentation to the original free target sheaf is a quasi-isomorphism.
`degreeTwoClass` is the literal derived roof obtained by inverting this
augmentation; an actual primitive supplies a null-homotopy and zero class.
Sheafification and the derived-category existence hypotheses stay explicit.

[CoverResolutionNaturality](CoverResolutionNaturality.lean) maps these same
tuples and resolutions along a commuting square of presheaf maps.
`resolutionAugmentation_naturality` retains the original augmentation and
free target map. `resolutionTupleLift_precomp` identifies precomposition under
the free/sheafification adjunctions, and `degreeTwoClass_precomp` identifies
the resulting derived roofs when both maps are locally surjective.
`resolutionMap_precomp_differential_eq` preserves literal primitives;
`degreeTwoCocycle_nullHomotopy_precomp` pulls back actual null-homotopies.
The alternating tuple differential and the cochain extension have the same
signs. No natural global splitting or enough-points hypothesis is introduced.

[Exactness](Exactness.lean), imported as
`Aglib.CategoryTheory.Sites.SheafCohomology.Cech.Exactness`, works over an
arbitrary category with finite products. `splitCech_exactAt_succ` gives
positive-degree exactness from a specified map of an actual terminal object
into a selected family member. `cechCosimplicialChangeIso` compares the original
Cech objects under a finite-product-preserving functor with thin target.
Abelian coefficients and the exact product-universe hypotheses stay explicit.

[Comparison](Comparison.lean) gives `cechCosimplicialCoefficientIso`,
`alternatingCofaceCoefficientIso` and `cechComplexCoefficientIso` for the actual
coefficient and alternating-coface comparisons. The cochain comparison retains
additivity and the stated product-preservation assumptions.

[ExactSequences](ExactSequences.lean) supplies the original differential formula
`cech_d_comp_π`, actual products of module short exact sequences and
`cech_shortExact_of_sections`. The last result assumes short exactness on all
finite products of the selected objects; a covering alone supplies no such
hypothesis. These statements contain no topological-space or sheaf condition.

[FiniteCoefficients](FiniteCoefficients.lean) separately gives the finite-family
coefficient comparisons for a finite-product-preserving coefficient functor.
Agreement with the all-product comparison retains the separately stated
`PreservesLimitsOfSize.{w,w}` premise.

[Topological Cech restriction and cocycles](../../../../Topology/Sheaves/Cech/README.md)
own the actual `TopCat`/`Opens X` specializations. Import those leaves directly
for open-intersection restriction, restricted exactness or the literal
pairwise/triple-intersection cocycle calculations. Their declarations retain
the native `CategoryTheory.Cech` namespace. Generic leaves do not import their
topological consumers.

[CoefficientNaturality](CoefficientNaturality.lean), imported as
`Aglib.CategoryTheory.Sites.SheafCohomology.Cech.CoefficientNaturality`, proves
`finiteCechComplexCoefficientIso_naturality_functor`: the original forward
finite Cech comparisons commute with any native natural transformation between
additive finite-product-preserving coefficient functors. The equation retains
the original product projections and independent category/product/index universes.
