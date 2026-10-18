# Generic site interfaces

The occupied cohomological family is [SheafCohomology](SheafCohomology/README.md). It works with actual site Cech objects and coefficient functors before any scheme specialization.

Main results are split-cover positive-degree exactness, actual coefficient/intersection comparisons and Cech short exact sequences from supplied sectionwise exactness. Abelian coefficients, product universes and the required cover/section data stay explicit. [Topological Cech theory](../../Topology/Sheaves/Cech/README.md) owns restricted-open comparisons and cocycle transport; [scheme cohomology](../../AlgebraicGeometry/Cohomology/README.md) owns structural field scalars and scheme-specialized comparison.

[Descent](Descent/README.md) transfers Mathlib's effective-descent predicate `Pseudofunctor.IsStackFor` along a transformation of pseudofunctors with equivalence components, and along a functor of sites that maps chosen pullbacks to pullbacks. Its consumer is the affine faithfully flat descent of quasi-coherent sheaves in [AlgebraicGeometry/Descent/Modules/Fppf](../../AlgebraicGeometry/Descent/Modules/Fppf/README.md).

[PresheafRepresentedDescent](PresheafRepresentedDescent.lean) constructs the
actual descent action from an adjunction and a supplied representation of the
restricted presheaf. The unit and associativity equations follow from the
adjunction triangles. Existence of the representing object remains an input.
