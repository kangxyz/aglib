# Site Cech cohomological support

[Cech](Cech/README.md) extends native `CategoryTheory.Cech` on actual Mathlib Cech complexes. Split covers give positive-degree exactness under the source's terminal-section and product hypotheses. Coefficient and intersection isomorphisms identify the original complexes, and supplied sectionwise short exactness yields the actual Cech short exact sequence. [Restricted-open comparisons and cocycles](../../../Topology/Sheaves/Cech/README.md) use topological spaces and live in the corresponding topological family.

The lower subjects are formal coproducts, abelian coefficients and actual sheaf/site functors. Scheme injective/affine Cech comparison is a later consumer; generic site statements contain no scheme, field or Noetherian premise unless stated by their coefficient interface.

## Slice and module coefficients

| Family | Reusable interface and current consumer |
| --- | --- |
| [Large](Large/README.md) | Large-valued original sheaf cohomology and injective suppliers; consumed by the actual small-etale slice entry. |
| [Slice](Slice/README.md) | Exact slice adjunction, free-representable Ext comparison, original maps and `H'`; concrete consumer is `Slice/Etale`. |
| [ModuleCoefficients](ModuleCoefficients/README.md) | Original module/abelian comparison, actual injective acyclicity, evaluation and slice maps; concrete consumer is `ModuleCoefficients.Etale`. |
| [Hypercohomology](../Hypercohomology/README.md) | Generic free-representable and degree-zero ordinary-cohomology comparison providers. |
