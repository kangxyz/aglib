# Abelian full subcategories

Import `Aglib.CategoryTheory.Abelian.Subcategory.Exact`. [Exact](Exact.lean) extends `CategoryTheory.ObjectProperty` with `Subcategory`, `subcategoryAbelian`, `subcategoryExactStructure`, `exactInclusion` and `inclusionFullyFaithful`.

For an object property in an abelian category, containing zero and closure under subobjects, quotients and finite products gives the actual abelian full subcategory. The inclusion preserves the relevant finite limits/colimits, is exact and fully faithful. Extension closure and `IsSerreClass` are not premises of this construction. `containsZero_iff_nonempty` gives the separate zero-object/nonempty comparison.

[Serre finite products](../SerreClass/README.md) supplies one way to obtain the product-closure input. Finite-module, ideal-killed and coherent categories consume these interfaces using their actual object properties and appropriate ring/scheme hypotheses.
