# Exact and abelian small models

The object is Mathlib's actual `CategoryTheory.SmallModel.{w} C`, for supplied `EssentiallySmall.{w} C`. The chosen universe `w` is part of the interface; the family does not prove smallness of arbitrary categories.

[Exact](Exact.lean) supplies `CategoryTheory.ExactCategory.ExactStructure.smallModel`, `smallModelToOriginal` and `originalToSmallModel`. They transport the actual additive/finite-biproduct structure and selected conflations through the small-model equivalence. [Abelian](Abelian.lean) supplies `CategoryTheory.ExactCategory.abelianExactStructure_smallModel`, identifying the transported exact structure with the standard abelian one.

[Functoriality](Functoriality.lean) supplies `CategoryTheory.ExactCategory.ExactFunctor.smallModel`, `smallModelIdIso`, `smallModelCompIso` and `smallModelNatIso`. The identity/composition statements are natural isomorphisms between choices, not strict equality of chosen models.

Focused imports are `Aglib.CategoryTheory.SmallModel.{Exact,Abelian,Functoriality}`. The main consumer is the actual locally Noetherian coherent category, whose stated sheaf-object universe bound must remain explicit. The lower prerequisite is [exact-structure equivalence transport](../ExactCategory/README.md).
