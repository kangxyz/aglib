# Exact and abelian small models

The object is Mathlib's actual `CategoryTheory.SmallModel.{w} C`, for supplied `EssentiallySmall.{w} C`. The chosen universe `w` is part of the interface; the family does not prove smallness of arbitrary categories.

[Exact](Exact.lean) supplies `CategoryTheory.ExactCategory.ExactStructure.smallModel`, `smallModelToOriginal` and `originalToSmallModel`. They transport the actual additive/finite-biproduct structure and selected conflations through the small-model equivalence. [Abelian](Abelian.lean) supplies `CategoryTheory.ExactCategory.abelianExactStructure_smallModel`, identifying the transported exact structure with the standard abelian one.

[Exact](Exact.lean) also owns `CategoryTheory.ExactCategory.ExactFunctor.smallModel`. [Functoriality](Functoriality.lean) supplies `smallModelIdIso`, `smallModelCompIso` and `smallModelNatIso`. The identity/composition statements are natural isomorphisms between choices, not strict equality of chosen models.

Focused imports are `Aglib.CategoryTheory.SmallModel.{Exact,Abelian,Functoriality}`. The main consumer is the actual locally Noetherian coherent category, whose stated sheaf-object universe bound must remain explicit. The lower prerequisite is [exact-structure equivalence transport](../ExactCategory/README.md).

[Functor](Functor.lean) conjugates the actual functor by the chosen Mathlib small-model
equivalences and compares its represented-object kernel. [Localization](Localization.lean)
transports the ordinary Serre localization. The same [Abelian](Abelian.lean) owner extends
its existing exact-structure comparison with `SmallModel.abelianExactComparison`,
`abelianExactComparison_isEquivalence` and `mapAbelianExactFunctor`, using the original
identity and conjugated functors.

[FunctorComparison](FunctorComparison.lean) adds `ExactCategory.ExactFunctor.smallModelSourceIso` for the
native exact-functor small model. It works for the original preadditive categories
with finite biproducts, retains `EssentiallySmall` in the specified target
universe, and compares the source presentations through the actual chosen
equivalence unit. The existing abelian `SmallModel.comparison` remains its own
interface.
