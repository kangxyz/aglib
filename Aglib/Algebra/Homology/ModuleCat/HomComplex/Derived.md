# A genuine fixed-coefficient derived dual

[Derived.lean](Derived.lean) constructs
`CochainComplex.HomComplex.derivedDual J` from the original A-module-valued
Hom functor when the actual coefficient complex J is K-injective. A is a
commutative ring. The coefficient-ring, module-carrier and selected
derived-category sizes remain explicit. No RHom, duality-data or
evaluation-isomorphism assumption is introduced.

The source quasi-isomorphism theorem in
[HomComplex.lean](../HomComplex.lean) proves that the original Hom functor
followed by native localization inverts A-quasi-isomorphisms. Native
localization along the opposite of `DerivedCategory.Q` then gives the
actual functor `D(A)^op → D(A)`. `derivedDualFactors` retains its original
comparison with the chain-level functor.

Original A-linearity of source precomposition descends through
`Localization.functor_linear_iff`. It also proves preservation of zero
morphisms. This does not rely on faithfulness of restriction from `D(A)`
to a smaller coefficient ring.
The explicit
[`CategoryTheory.Linear.opposite`](../../../../CategoryTheory/Linear/Opposite.lean)
structure transports the
original Hom scalars through native `unop`; this leaf uses it locally for
the two opposite categories. It introduces no new action on the complexes.

`derivedEvaluation` is the localization of the signed A-linear chain
evaluation from [Evaluation.lean](Evaluation.lean). Its target is the
actual double composite `(derivedDual J).rightOp ⋙ derivedDual J`.
`derivedDoubleDualFactors` retains both occurrences of the original
single-dual comparison, including their contravariant direction.
`derivedEvaluation_app_Q` states the precise original chain-map formula
for its value on every localized representative.

In the surface application, J is the actual coinduced image of a chosen
injective R-resolution of R. Exact coinduction identifies its augmentation
with `Hom_R(A,R)` and preservation of injectives gives K-injectivity.
Those existing suppliers justify the coefficient hypothesis; a new
unproved surface-duality property is not substituted.

This file constructs the dual and evaluation. Invertibility of evaluation
on finite R-perfect restrictions, the actual nonsplit C model, surface
concentration and the original trace comparison remain separate
obligations. The current consumer is that genuine A-derived evaluation
argument; no GR or B7 uniform-annihilator conclusion is asserted.

Source basis: Aglib `8b93cc5940dc93f39a2eaf05e6985af28250a578`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1. Native compilation
is coordinated by the principal; coupled proof repair stays with the author.
