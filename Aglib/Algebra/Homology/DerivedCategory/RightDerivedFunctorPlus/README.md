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

[SingleHomology](SingleHomology.lean) identifies the original natural-degree
`F.rightDerived n` with homology of the installed bounded-below `RF` at the
native degree-zero single. `Functor.rightDerivedSingleHomologyIso` applies
to every additive functor between the specified abelian derived categories,
with enough injectives in the source and independent category universes.
Its `_hom_app` formula works for every supplied original injective resolution:
the native integer-resolution homology comparison is followed by inverse
localization/homology factorization and homology of the original derived-unit
comparison. The pointwise map is natural for every native resolution lift,
so no new cohomology or resolution model is introduced.
`rightDerivedSingleHomologyZeroIso` additionally retains preservation of finite
limits; its forward and inverse equations are the original native
`rightDerivedZeroIsoSelf` and `toRightDerivedZero` maps.

[TStructure](TStructure.lean) proves that the installed right-derived
functor preserves every native lower cohomological bound, for an arbitrary
additive functor between the stated abelian categories. Left exactness and
homology preservation are not assumed. The proof uses the native
termwise-injective representative in the same lower range, the original
invertible derived unit and its actual image isomorphism. Native homology
below the retained bound is therefore zero. The source and target category,
morphism and derived-category universes remain independent. Shared
Postnikov arguments for flat base change and bounded coherent direct
images consume these bounds.

For an exact additive functor,
`rightDerivedFunctorPlusSingleIso F i` carries the native single in any integer
degree through the installed `RF`. Its `_unit` equation is the actual original
derived unit followed by the original single-complex comparison. It introduces
no second derived-functor model. Derived open locality consumes this interface.

[Composition/Shift](Composition/Shift.lean) retains native shift compatibility
of the original two-functor unit, independently of the separate sufficient
hypotheses making that unit derive composition.

[AcyclicSingle](AcyclicSingle.lean) provides
`rightDerivedFunctorPlusSingleIsoOfAcyclic F M hM` for a left exact
additive functor and a chosen coefficient whose original positive
`F.rightDerived` objects vanish. It identifies the actual installed `RF`
of the degree-zero native single with the native single of `F.obj M`.
Its forward map is the inverse of the original derived unit followed by
the original single-complex comparison. The `_unit` equation and original
coefficient-map naturality retain these maps. Every supplied native
injective resolution proves invertibility of the same unit using the
sole lower mapped-augmentation theorem; no full homology preservation
or target resolution is assumed. The source passed with receipt
`1792118629133708000-91272` in 2.4 seconds at the default budget. The
independent six-universe `AcyclicDerivedSingleConsumer.lean` passed with
receipt `1792118659907779000-91729`; all four inspected declarations use
only the three standard axioms. Affine direct images of quasicoherent
coefficients and their finite-morphism coherent specializations consume
this comparison.

## Etale cohomology comparisons

The [actual right-derived Ext comparison](../ExtRightDerived.lean) and
[adjunction interfaces](Adjunction.lean) supply the bounded-below comparison
used by the scheme-specific [etale derived cohomology family](../../../../AlgebraicGeometry/EtaleCohomology/README.md).
The resulting canonical `D+` and global-sections comparison retains the actual
right-derived adjunction and unit. Higher maps and their degree-zero ordinary
normalization are recorded by the consumer. The D continuation also supplies
[HigherHorizontalDiagram](BaseChange/HigherHorizontalDiagram.lean),
[HigherWholePasting](BaseChange/HigherWholePasting.lean), and
[WholeNormalization](BaseChange/WholeNormalization.lean). The ordinary
`baseChangeMap_hComp`, `_vComp`, and `_vId` equations retain the native
inverse-image/direct-image composition comparisons. The derived
`derivedBaseChangeMap_hComp`, `_vComp`, and `_vId` equations retain the actual
`D+` mates, adjunctions, and direct-image composition maps. The all-degree
`higherBaseChangeMap_hComp`, `_vComp`, and `_vId` equations pass through the
native higher source/target comparisons and homology of actual composite
images. The vertical identity uses the native comparison and does not identify
positive-degree derived image of an identity with the identity functor. The
original H1 square is also supplied by `h1Pullback_square` and its canonical
mate form `derivedBaseChangeMap_h1_square`. These identities do not assert
exchange-map invertibility, proper base change, or unbounded derived scope. The independent `derived_archive_review` accepted the selected D sources;
the principal-owned selected integration checks passed. See the
migration note for the exact claim boundary.

## Scalar-forgetting exchange cubes

`BaseChange/ExactIsoCube`, `ExactMateCube`, `MateCubeComponent` and
`MateCubeIsomorphism` retain the original exact comparisons and mates of a
whole cube before deriving. `Conservative` proves reflection of isomorphisms
for the actual exact derived functor. Their geometric consumer is the
original genuine-module scalar-forgetting exchange square and finite base
change in `EtaleCohomology/Exceptional/Derived`, with independent models.
