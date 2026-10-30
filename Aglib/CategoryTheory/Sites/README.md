# Generic site interfaces

The occupied cohomological family is [SheafCohomology](SheafCohomology/README.md). It works with actual site Cech objects and coefficient functors before any scheme specialization.

Main results are split-cover positive-degree exactness, actual coefficient/intersection comparisons and Cech short exact sequences from supplied sectionwise exactness. Abelian coefficients, product universes and the required cover/section data stay explicit. [Topological Cech theory](../../Topology/Sheaves/Cech/README.md) owns restricted-open comparisons and cocycle transport; [scheme cohomology](../../AlgebraicGeometry/Cohomology/README.md) owns structural field scalars and scheme-specialized comparison.

[Descent](Descent/README.md) transfers Mathlib's effective-descent predicate `Pseudofunctor.IsStackFor` along a transformation of pseudofunctors with equivalence components, and along a functor of sites that maps chosen pullbacks to pullbacks. Its consumer is the affine faithfully flat descent of quasi-coherent sheaves in [AlgebraicGeometry/Descent/Modules/Fppf](../../AlgebraicGeometry/Descent/Modules/Fppf/README.md).

[PresheafRepresentedDescent](PresheafRepresentedDescent.lean) constructs the
actual descent action from an adjunction and a supplied representation of the
restricted presheaf. The unit and associativity equations follow from the
adjunction triangles. Existence of the representing object remains an input.

[OverMapCovering](OverMapCovering.lean): for a Grothendieck topology `J` on `C` and `f : X ⟶ Y`, a
sieve `R` on `U : Over X` covers for `J.over X` if and only if `R.functorPushforward (Over.map f)`
covers for `J.over Y` (`GrothendieckTopology.functorPushforward_over_map_mem_iff`), and a sieve on
`(Over.map f).obj U` covers if and only if its preimage under `Over.map f` does
(`GrothendieckTopology.functorPullback_over_map_mem_iff`); both say that the generated sieve of
`U.left` covers for `J`. These are the two directions behind Mathlib's continuity and cocontinuity
instances of `Over.map f`. Consumer:
[Picard/BaseChange](../../AlgebraicGeometry/Picard/BaseChange.lean).

[Constant-sheaf units](ConstantSheaf/Unit.lean) retain the original
`constantSheafAdj` unit under a coefficient functor preserving sheafification.
At a supplied terminal object, the actual constant-composition isomorphism
identifies the two units. If the coefficient functor reflects isomorphisms,
invertibility of the target unit implies invertibility of the original unit.
The etale module consumer supplies its original torsion-unit geometric theorem.

[Constant cohomology transport](ConstantRestriction/Cohomology.lean) uses the
original constant-adjunction comparison at both the integer generator and the
coefficient value. Its identity, composition and triangle laws follow from the
whole adjunction coherence, preserving independent Ext worlds. The underived
constant-restriction interface keeps its separate, narrower imports.

[Torsor chart trivialization](Torsor/ChartTrivialization.lean) restricts the
same carrier and action to an actual site slice, then uses the supplied local
section for its original section-equivalence trivialization.
[Coefficient isomorphisms](Torsor/CoefficientIso.lean) retain the literal
carrier with the inverse coefficient action.
[Torsor functoriality](Torsor/Functoriality.lean) uses actual coefficient
pushouts and inverse-image carriers on isomorphism classes, with their stated
sheafification and Ext hypotheses. The class formulas retain those actual
representatives.

[OverProducts](RepresentedTransfer/OverProducts.lean) constructs pullback product
tests in a full morphism-property Over category, their maps, symmetry and
terminal/counit laws. Comparison with a chosen categorical product preserves
both original projections, under the stated pullback and stability hypotheses.

[Point germ values](Point/Germ.lean) retain the literal germs of native point morphisms. [Represented additive evaluation](Point/RepresentedAdditive.lean) uses the original lifted additive sections and actual point fibre, with the stated full-inclusion and colimit premises. [Section values](Point/SectionValues.lean) assembles the original section and germ squares and cancels the actual invertible chart component. No additional point, section functor or derived realization is chosen.
