# Generic Cech exactness and coefficient comparison

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
