# Site Cech cohomological support

[Cech](Cech/README.md) extends native `CategoryTheory.Cech` on actual Mathlib Cech complexes. Split/restricted covers give positive-degree exactness under the source's terminal-section and product hypotheses. Coefficient and intersection isomorphisms identify the original complexes, and supplied sectionwise short exactness yields the actual Cech short exact sequence.

The lower subjects are formal coproducts, abelian coefficients and actual sheaf/site functors. Scheme injective/affine Cech comparison is a later consumer; generic site statements contain no scheme, field or Noetherian premise unless stated by their coefficient interface.
