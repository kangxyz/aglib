# Finite products in a Serre class

[FiniteProducts](FiniteProducts.lean), imported as `Aglib.CategoryTheory.Abelian.SerreClass.FiniteProducts`, supplies `CategoryTheory.ObjectProperty.serre_isClosedUnderFiniteProducts`. A genuine `IsSerreClass` in an abelian category is closed under finite products, using the actual biproduct short exact sequence and extension closure.

This result supplies the finite-product premise of [the abelian subcategory construction](../Subcategory/README.md). It does not identify every abelian full subcategory with a Serre class. Finite modules over a Noetherian ring are a concrete consumer.

[Exact](Exact.lean) bundles an additive Serre localization as the selected exact functor
between the standard abelian exact structures, with independent source and target
universes. It reuses Mathlib's actual quotient category and its abelian structure.
