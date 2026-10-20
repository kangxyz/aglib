# Finite products in a Serre class

[FiniteProducts](FiniteProducts.lean), imported as `Aglib.CategoryTheory.Abelian.SerreClass.FiniteProducts`, supplies `CategoryTheory.ObjectProperty.serre_isClosedUnderFiniteProducts`. A genuine `IsSerreClass` in an abelian category is closed under finite products, using the actual biproduct short exact sequence and extension closure.

This result supplies the finite-product premise of [the abelian subcategory construction](../Subcategory/README.md). It does not identify every abelian full subcategory with a Serre class. Finite modules over a Noetherian ring are a concrete consumer.

[Exact](Exact.lean) bundles an additive Serre localization as the selected exact functor
between the standard abelian exact structures, with independent source and target
universes. It reuses Mathlib's actual quotient category and its abelian structure.

[ExactKernels](ExactKernels.lean) proves the Serre property of the actual kernel of a selected exact
functor between standard abelian exact structures, and arbitrary intersections
of Serre classes. Its canonical `ExactCategory.ExactFunctor` instances recover
finite-limit and finite-colimit preservation from conflation preservation, with
independent source/target object and hom universes.

[PairFunctor](PairFunctor.lean) restricts an actual exact functor preserving a pair of Serre classes
and constructs its Gabriel-quotient lift. The inclusion and quotient
factorizations are equalities of the literal underlying functors. The
Serre-preservation hypothesis and the source's common category/hom universe
remain explicit. Its bundled exact functors are the selected
`CategoryTheory.ExactCategory.ExactFunctor` interface.
