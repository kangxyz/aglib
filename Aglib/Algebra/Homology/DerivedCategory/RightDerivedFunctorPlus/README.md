# Original right-derived identity and composition comparisons

[Composition](Composition.lean), imported as `Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition`, constructs `CategoryTheory.Functor.rightDerivedFunctorPlusCompUnit` on the actual bounded-below objects. The two comparison isomorphisms have separate sufficient hypotheses: `rightDerivedFunctorPlusCompIsoOfPreservesInjectives` requires the first functor to preserve injectives; `rightDerivedFunctorPlusCompIsoOfPreservesHomology` requires the second functor to preserve homology. Additivity, enough-injective/derived-category availability and the original units remain those of the source statement.

Each hom-component equation uses the installed right-derived unit, rather than an arbitrary choice of comparison. [Identity](Identity.lean) constructs `rightDerivedFunctorPlusIdIso` and `rightDerivedFunctorPlusIdIso_unit` from the original identity comparison.

Consumers are [one-sided derived contraction](../Plus/README.md), actual scheme pushforward composition, Godement calculation and derived projection formula. Neither composition branch may be used without its corresponding preservation hypothesis.

[Homology](Homology.lean), imported as `Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Homology`, constructs `CategoryTheory.Functor.mapCochainComplexPlusHomologyIso` for an additive functor preserving homology. With `EnoughInjectives` in the source and derived categories for both abelian categories, `rightDerivedFunctorPlusHomologyIso` compares the actual right-derived functor followed by homology with homology followed by the original functor. `rightDerivedFunctorPlusHomologyIso_unit` preserves the installed unit and the original complex homology maps. `DerivedCategory.Plus.homologyFunctorFactors` supplies the comparison through the actual bounded-below localization. This result does not assert such a calculation for an arbitrary additive functor.

[InjectiveResolution](InjectiveResolution.lean) instead uses a supplied actual
native injective resolution for an arbitrary additive functor between abelian
categories with the indicated derived categories and enough injectives in the
source. `InjectiveResolution.rightDerivedFunctorPlusIso F I` identifies the
localized termwise image of `I.cochainComplexPlus` with the installed
`F.rightDerivedFunctorPlus` at the original degree-zero single. Its forward
map is literally the installed derived unit followed by the inverse image of
`Q.map I.ιPlus`, where `I.ιPlus` is the original `I.ι'`. The original unit
equation and coefficient naturality hold for every supplied native resolution
lift. No homology-preservation assumption on `F` is needed for this model.
