# Exceptional direct image

This family develops extension by zero and exceptional direct images on the
actual small-etale site. It uses the native sheaf, module, complex and derived
category carriers and retains the original adjunction maps. This is an active
implementation, not a completed exceptional calculus.

## Current source families

- `Open/`: actual abelian lower shriek from the existing slice equivalence and
  hom-indexed coproduct/sheafification construction; adjunction, exactness,
  open full faithfulness/stalks, and comparisons are being implemented.
  Abelian source is an intermediate supplier, not the arbitrary-ring endpoint.
  [LowerShriekExt](Open/LowerShriekExt.lean) retains the original exact-functor
  and adjunction Ext APIs.
- `Coefficients/`: actual constant ring sheaves, genuine `SheafOfModules`, and
  comparisons with module-valued sheaves. The standard explicit scalar/value
  range is `u+1` for schemes in `u`. No torsion or Noetherian condition belongs
  to these ordinary constructions. Native pullback/pushforward and original
  units must be compared, not replaced by unrelated functors.

- `Derived/`: native bounded-below ordinary module direct images and the
  original derived adjunction/unit, as suppliers for exceptional comparisons;
  this does not assert proper base change or choice independence.

- `Refinement/`: the actual original-derived-unit map for a proper refinement,
  using its genuine Cartesian open square. The original transformation now
  satisfies identity and composition coherence. Its torsion invertibility and
  compactification independence use the native proper-base-change and
  compactification-comparison interfaces.

The associated compactification geometry belongs to
`AlgebraicGeometry/Compactification/Refinements`; genuine unbounded replacement
existence belongs to `Algebra/Homology/DerivedCategory/KInjective/Existence`.
The native unbounded image consumer uses the completed functorial K-injective
replacement and its original natural quasi-isomorphism, not a supplied-model
hypothesis or only a first injective successor operation.

[BoundedBelow/Composition](BoundedBelow/Composition.lean) constructs the
original exceptional compositor, using the proper/open adjunction mate and
the original open and proper compositors. Its compactification comparisons
retain the original maps. [CompositionAssociativity](BoundedBelow/CompositionAssociativity.lean)
identifies the two triple-composition routes with the original scheme-arrow
transport. These statements use arbitrary ring coefficients on intrinsic
torsion bounded-below objects, with the displayed geometric and independent
compactification-model hypotheses.

[Unbounded/ExceptionalCoproducts](Unbounded/ExceptionalCoproducts.lean) proves
that the same chosen unbounded exceptional functor preserves coproducts
indexed in the coefficient universe. Its original `sigmaComparison` is
invertible and retains the original coproduct inclusions. The theorem keeps
the positive annihilator of the coefficient unit and its stated
quasi-compact and quasi-separated geometric range.

## Completion boundaries

A definition from one compactification does not prove independence. The intended
bounded-below torsion calculus must include actual unit-induced comparisons,
choice independence, identity/composition coherence, original arbitrary base
change, localization and proper/open normalizations.

Unbounded work uses a torsion ring with a positive annihilator of its unit,
without requiring invertibility on the base. The actual functorial
K-injective replacement, original unbounded direct image and adjunction, exact
open image, and original unbounded localization triangle are supplied.
Finite-dimensional acyclic computation and
[unbounded proper exchange](Unbounded/ProperBaseChangeTheorem.lean) have
separate interfaces with their actual bound and model hypotheses. No finite
absolute dimension of the base is assumed.

Proper base change and relative cohomological bounds retain their own source
hypotheses. Construction and coherence of an exchange alone do not establish
its invertibility. `Proper`, `Finite`, `Constructible`, Nagata and ordinary
exchange sources supply their respective geometric inputs. Generic coefficient
pullback constructions use their native site owner.

Precise current acceptance is recorded separately with successful source hashes
and native receipts; uncompiled source is not described here as a closed result.
Generated imports and shared publication are serialized by the principal.

The ordinary module comparison adapters use the complete categorical
original-unit, selected-adjoint and source-pasting constructions. Their
valued comparisons retain the original coefficient equivalences and
preimage maps. The derived underlying mate is the canonical three-factor
comparison from exact forgetting and the existing relative-acyclicity
argument. The dense refinement map uses the same lower comparison-pasting
constructor. These interfaces preserve the existing coefficient ranges and
selected worlds; their publication does not assert the remaining torsion,
localization or chosen-exceptional coherence endpoints.

[Open/ModuleStalk](Open/ModuleStalk.lean) specializes the [general constant-ring point fibre](../../../Algebra/Category/ModuleCat/Sheaf/ConstantRing/PointFibre.lean) to the actual native site and coefficient worlds. The underlying additive comparison and outside-open zero-stalk conclusion use the original coefficient forgetting and original lower-shriek stalk.

[ModuleUnderlyingCoherence](Open/ModuleUnderlyingCoherence.lean) and
[ModuleUnderlyingComposition](Open/ModuleUnderlyingComposition.lean) retain
the original lower-shriek unit, counit and comparison-chain equations.

The original module-slice and scalar-restriction comparisons in [Open/ModuleSliceUnderlying](Open/ModuleSliceUnderlying.lean) and [Open/ModuleScalarRestriction](Open/ModuleScalarRestriction.lean) specialize the complete forward comparison and preserve its original coefficient and unit/counit maps. [Open/Stalk](Open/Stalk.lean) proves the outside-open zero-stalk result from the actual empty point fibre and the existing lower-shriek/skyscraper adjunctions, with the original open and no-lift conditions.

Finite module base change retains its four genuine module derived worlds;
auxiliary abelian realizations needed only in its proof are chosen locally.
The original homology and lower-shriek underlying isomorphisms transport
internal per-degree or local-annihilator torsion without a uniform exponent
or a preservation-of-injectives assumption on scalar forgetting.
The bounded-below and full-unbounded localization consumers use whole
first/third vertex comparisons with the original open counit, closed unit
and mapping-cone connecting map. Full-unbounded localization gains no
lower-bound or finite-cohomological-dimension premise. These statements
do not assert an additional chosen exceptional coherence calculus.

[Finite/LowerShriek](Finite/LowerShriek.lean) proves invertibility of the
original finite-étale lower-shriek/direct-image comparison and its original
unit, counit and canonical trace laws under the stated separatedness and
finite-rank hypotheses. [ModuleComparison](Finite/ModuleComparison.lean)
and [ModuleTraceNormalization](Finite/ModuleTraceNormalization.lean) lift
the same maps through original scalar forgetting, including levels zero
and one.

## Additional source entry points

Each source states the exact hypotheses, maps, and realization bounds of its interfaces.

- [BoundedBelow/BaseChangeCompositionOriginal](BoundedBelow/BaseChangeCompositionOriginal.lean)
- [BoundedBelow/BaseChangeComposition](BoundedBelow/BaseChangeComposition.lean)
- [BoundedBelow/BaseChangeModelIdentity](BoundedBelow/BaseChangeModelIdentity.lean)
- [BoundedBelow/BaseChangeTargetModels](BoundedBelow/BaseChangeTargetModels.lean)
- [BoundedBelow/CartesianBaseChangeGeometry](BoundedBelow/CartesianBaseChangeGeometry.lean)
- [BoundedBelow/CartesianBaseChangeLiteralAlgebra](BoundedBelow/CartesianBaseChangeLiteralAlgebra.lean)
- [BoundedBelow/CartesianBaseChangeLiteralTorsion](BoundedBelow/CartesianBaseChangeLiteralTorsion.lean)
- [BoundedBelow/CartesianBaseChangeLiteral](BoundedBelow/CartesianBaseChangeLiteral.lean)
- [BoundedBelow/CartesianCompositionCanonical](BoundedBelow/CartesianCompositionCanonical.lean)
- [BoundedBelow/CartesianCompositionIdentity](BoundedBelow/CartesianCompositionIdentity.lean)
- [BoundedBelow/CartesianCompositionMap](BoundedBelow/CartesianCompositionMap.lean)
- [BoundedBelow/CartesianFirstComparison](BoundedBelow/CartesianFirstComparison.lean)
- [BoundedBelow/CartesianFirstCube](BoundedBelow/CartesianFirstCube.lean)
- [BoundedBelow/CartesianFirstHorizontal](BoundedBelow/CartesianFirstHorizontal.lean)
- [BoundedBelow/CartesianFirstNaturality](BoundedBelow/CartesianFirstNaturality.lean)
- [BoundedBelow/CartesianFirstRectangle](BoundedBelow/CartesianFirstRectangle.lean)
- [BoundedBelow/CartesianFirstStructural](BoundedBelow/CartesianFirstStructural.lean)
- [BoundedBelow/CartesianFirstTargetComparison](BoundedBelow/CartesianFirstTargetComparison.lean)
- [BoundedBelow/CartesianUnderlyingMap](BoundedBelow/CartesianUnderlyingMap.lean)
- [BoundedBelow/ChosenIdentityNormalization](BoundedBelow/ChosenIdentityNormalization.lean)
- [BoundedBelow/ChosenLeftUnitContraction](BoundedBelow/ChosenLeftUnitContraction.lean)
- [BoundedBelow/CompositionAssociativity](BoundedBelow/CompositionAssociativity.lean)
- [BoundedBelow/CompositionBCModelComparison](BoundedBelow/CompositionBCModelComparison.lean)
- [BoundedBelow/CompositionHorizontalPasting](BoundedBelow/CompositionHorizontalPasting.lean)
- [BoundedBelow/CompositionInterchange](BoundedBelow/CompositionInterchange.lean)
- [BoundedBelow/CompositionLeftUnitExpansion](BoundedBelow/CompositionLeftUnitExpansion.lean)
- [BoundedBelow/CompositionLeftUnitFace](BoundedBelow/CompositionLeftUnitFace.lean)
- [BoundedBelow/CompositionLeftUnitIdentity](BoundedBelow/CompositionLeftUnitIdentity.lean)
- [BoundedBelow/CompositionLeftUnitImage](BoundedBelow/CompositionLeftUnitImage.lean)
- [BoundedBelow/CompositionLeftUnitSource](BoundedBelow/CompositionLeftUnitSource.lean)
- [BoundedBelow/CompositionLeftUnitTransport](BoundedBelow/CompositionLeftUnitTransport.lean)
- [BoundedBelow/CompositionLeftUnit](BoundedBelow/CompositionLeftUnit.lean)
- [BoundedBelow/CompositionMixedRefinementFaces](BoundedBelow/CompositionMixedRefinementFaces.lean)
- [BoundedBelow/CompositionMixedRefinementWhole](BoundedBelow/CompositionMixedRefinementWhole.lean)
- [BoundedBelow/CompositionModelComparison](BoundedBelow/CompositionModelComparison.lean)
- [BoundedBelow/CompositionModelMaps](BoundedBelow/CompositionModelMaps.lean)
- [BoundedBelow/CompositionModel](BoundedBelow/CompositionModel.lean)
- [BoundedBelow/CompositionRawSquare](BoundedBelow/CompositionRawSquare.lean)
- [BoundedBelow/CompositionRefinementAdapters](BoundedBelow/CompositionRefinementAdapters.lean)
- [BoundedBelow/CompositionRefinementCube](BoundedBelow/CompositionRefinementCube.lean)
- [BoundedBelow/CompositionRefinementDirectImage](BoundedBelow/CompositionRefinementDirectImage.lean)
- [BoundedBelow/CompositionRefinementFaces](BoundedBelow/CompositionRefinementFaces.lean)
- [BoundedBelow/CompositionRefinementHorizontal](BoundedBelow/CompositionRefinementHorizontal.lean)
- [BoundedBelow/CompositionRefinement](BoundedBelow/CompositionRefinement.lean)
- [BoundedBelow/CompositionRightUnitFace](BoundedBelow/CompositionRightUnitFace.lean)
- [BoundedBelow/CompositionRightUnitImage](BoundedBelow/CompositionRightUnitImage.lean)
- [BoundedBelow/CompositionRightUnitMiddleComparison](BoundedBelow/CompositionRightUnitMiddleComparison.lean)
- [BoundedBelow/CompositionRightUnitMiddle](BoundedBelow/CompositionRightUnitMiddle.lean)
- [BoundedBelow/CompositionRightUnitOpenFace](BoundedBelow/CompositionRightUnitOpenFace.lean)
- [BoundedBelow/CompositionRightUnitOpen](BoundedBelow/CompositionRightUnitOpen.lean)
- [BoundedBelow/CompositionRightUnitProperFace](BoundedBelow/CompositionRightUnitProperFace.lean)
- [BoundedBelow/CompositionRightUnitSource](BoundedBelow/CompositionRightUnitSource.lean)
- [BoundedBelow/CompositionRightUnitStructural](BoundedBelow/CompositionRightUnitStructural.lean)
- [BoundedBelow/CompositionRightUnit](BoundedBelow/CompositionRightUnit.lean)
- [BoundedBelow/CompositionSingleModelFormula](BoundedBelow/CompositionSingleModelFormula.lean)
- [BoundedBelow/CompositionSingleModelUnderlying](BoundedBelow/CompositionSingleModelUnderlying.lean)
- [BoundedBelow/CompositionSingleModel](BoundedBelow/CompositionSingleModel.lean)
- [BoundedBelow/CompositionSingleSource](BoundedBelow/CompositionSingleSource.lean)
- [BoundedBelow/CompositionSingleTarget](BoundedBelow/CompositionSingleTarget.lean)
- [BoundedBelow/CompositionTripleInterchange](BoundedBelow/CompositionTripleInterchange.lean)
- [BoundedBelow/Composition](BoundedBelow/Composition.lean)
- [BoundedBelow/FamilyArrowComparison](BoundedBelow/FamilyArrowComparison.lean)
- [BoundedBelow/FamilyCongruence](BoundedBelow/FamilyCongruence.lean)
- [BoundedBelow/FamilyModelComparison](BoundedBelow/FamilyModelComparison.lean)
- [BoundedBelow/IdentityFactorizationCoherence](BoundedBelow/IdentityFactorizationCoherence.lean)
- [BoundedBelow/Identity](BoundedBelow/Identity.lean)
- [BoundedBelow/LeftUnitSourceExpansion](BoundedBelow/LeftUnitSourceExpansion.lean)
- [BoundedBelow/LeftUnitSourceRestriction](BoundedBelow/LeftUnitSourceRestriction.lean)
- [BoundedBelow/LeftUnitSupplied](BoundedBelow/LeftUnitSupplied.lean)
- [BoundedBelow/LeftUnitTorsionSupplied](BoundedBelow/LeftUnitTorsionSupplied.lean)
- [BoundedBelow/LeftUnitTotalComparison](BoundedBelow/LeftUnitTotalComparison.lean)
- [BoundedBelow/LocalizationComposition](BoundedBelow/LocalizationComposition.lean)
- [BoundedBelow/Localization](BoundedBelow/Localization.lean)
- [BoundedBelow/Normalization](BoundedBelow/Normalization.lean)
- [BoundedBelow/NormalizedToDirectImageBaseChange](BoundedBelow/NormalizedToDirectImageBaseChange.lean)
- [BoundedBelow/OpenNormalizationComparison](BoundedBelow/OpenNormalizationComparison.lean)
- [BoundedBelow/ProperNormalizationComparison](BoundedBelow/ProperNormalizationComparison.lean)
- [BoundedBelow/RawComparisonToDirectImage](BoundedBelow/RawComparisonToDirectImage.lean)
- [BoundedBelow/RawToDirectImageBaseChange](BoundedBelow/RawToDirectImageBaseChange.lean)
- [BoundedBelow/RawToDirectImage](BoundedBelow/RawToDirectImage.lean)
- [BoundedBelow/RightUnitChosenTarget](BoundedBelow/RightUnitChosenTarget.lean)
- [BoundedBelow/RightUnitSuppliedComparison](BoundedBelow/RightUnitSuppliedComparison.lean)
- [BoundedBelow/RightUnitSupplied](BoundedBelow/RightUnitSupplied.lean)
- [BoundedBelow/RightUnitTorsionSupplied](BoundedBelow/RightUnitTorsionSupplied.lean)
- [BoundedBelow/RightUnitTotalComparison](BoundedBelow/RightUnitTotalComparison.lean)
- [BoundedBelow/SourceIsoIdentity](BoundedBelow/SourceIsoIdentity.lean)
- [BoundedBelow/SuppliedComposition](BoundedBelow/SuppliedComposition.lean)
- [BoundedBelow/TargetModelComparison](BoundedBelow/TargetModelComparison.lean)
- [BoundedBelow/ToDirectImageBaseChange](BoundedBelow/ToDirectImageBaseChange.lean)
- [BoundedBelow/ToDirectImageCompositionModel](BoundedBelow/ToDirectImageCompositionModel.lean)
- [BoundedBelow/ToDirectImageComposition](BoundedBelow/ToDirectImageComposition.lean)
- [BoundedBelow/ToDirectImageNaturality](BoundedBelow/ToDirectImageNaturality.lean)
- [BoundedBelow/ToDirectImageOfNonempty](BoundedBelow/ToDirectImageOfNonempty.lean)
- [BoundedBelow/ToDirectImage](BoundedBelow/ToDirectImage.lean)
- [BoundedBelow/TripleCartesianComposition](BoundedBelow/TripleCartesianComposition.lean)
- [BoundedBelow/TripleCartesianLeftRoute](BoundedBelow/TripleCartesianLeftRoute.lean)
- [BoundedBelow/TripleCartesianMaps](BoundedBelow/TripleCartesianMaps.lean)
- [BoundedBelow/TripleCartesianRightRoute](BoundedBelow/TripleCartesianRightRoute.lean)
- [BoundedBelow/TripleChosenTotalComparison](BoundedBelow/TripleChosenTotalComparison.lean)
- [BoundedBelow/TripleFirstComparisons](BoundedBelow/TripleFirstComparisons.lean)
- [BoundedBelow/TripleHorizontalOpenTransport](BoundedBelow/TripleHorizontalOpenTransport.lean)
- [BoundedBelow/TripleOpenContraction](BoundedBelow/TripleOpenContraction.lean)
- [BoundedBelow/TripleRawComposition](BoundedBelow/TripleRawComposition.lean)
- [BoundedBelow/TripleSingleModelAssociativity](BoundedBelow/TripleSingleModelAssociativity.lean)
- [BoundedBelow/TripleSingleModels](BoundedBelow/TripleSingleModels.lean)
- [BoundedBelow/TripleTotalArrowComparison](BoundedBelow/TripleTotalArrowComparison.lean)
- [BoundedBelow/TripleTotalComparison](BoundedBelow/TripleTotalComparison.lean)
- [BoundedBelow/UnitIdentityValue](BoundedBelow/UnitIdentityValue.lean)
- [BoundedBelow/UnitModelArrow](BoundedBelow/UnitModelArrow.lean)
- [BoundedBelow/UnitModelComparison](BoundedBelow/UnitModelComparison.lean)
- [BoundedBelow/UnitModelFamily](BoundedBelow/UnitModelFamily.lean)
- [BoundedBelow/UnitModelNormalization](BoundedBelow/UnitModelNormalization.lean)
- [BoundedBelow/UnitModelTorsionMap](BoundedBelow/UnitModelTorsionMap.lean)
- [BoundedBelow/UnitModelTorsionRefinement](BoundedBelow/UnitModelTorsionRefinement.lean)
- [BoundedBelow/UnitModelTorsion](BoundedBelow/UnitModelTorsion.lean)
- [Compactification/BaseChangeIdentityAlgebra](Compactification/BaseChangeIdentityAlgebra.lean)
- [Compactification/BaseChangeIdentityCompatibility](Compactification/BaseChangeIdentityCompatibility.lean)
- [Compactification/ComparisonFormulas](Compactification/ComparisonFormulas.lean)
- [Compactification/CompositionBCChosenModel](Compactification/CompositionBCChosenModel.lean)
- [Compactification/CompositionBCModelSquare](Compactification/CompositionBCModelSquare.lean)
- [Compactification/CompositionBCNormalization](Compactification/CompositionBCNormalization.lean)
- [Compactification/CompositionBCRawSource](Compactification/CompositionBCRawSource.lean)
- [Compactification/CompositionBCRefinement](Compactification/CompositionBCRefinement.lean)
- [Compactification/CompositionBCRestriction](Compactification/CompositionBCRestriction.lean)
- [Compactification/CompositionBCTorsion](Compactification/CompositionBCTorsion.lean)
- [Compactification/CompositionBaseChangeCube](Compactification/CompositionBaseChangeCube.lean)
- [Compactification/CompositionBaseChangeExchange](Compactification/CompositionBaseChangeExchange.lean)
- [Compactification/CompositionBaseChangeModel](Compactification/CompositionBaseChangeModel.lean)
- [Compactification/CompositionBaseChangePasting](Compactification/CompositionBaseChangePasting.lean)
- [Compactification/FamilyModelComparison](Compactification/FamilyModelComparison.lean)
- [Compactification/FamilyModelDiagram](Compactification/FamilyModelDiagram.lean)
- [Compactification/IdentityAmbientComparison](Compactification/IdentityAmbientComparison.lean)
- [Compactification/IdentityAmbientOpenComparison](Compactification/IdentityAmbientOpenComparison.lean)
- [Compactification/NormalizedTargetModels](Compactification/NormalizedTargetModels.lean)
- [Compactification/RawBaseChangeTargetModels](Compactification/RawBaseChangeTargetModels.lean)
- [Compactification/RawComparisonCongruence](Compactification/RawComparisonCongruence.lean)
- [Compactification/RawTargetModels](Compactification/RawTargetModels.lean)
- [Compactification/SourceIsoIdentity](Compactification/SourceIsoIdentity.lean)
- [Compactification/TargetModelComparison](Compactification/TargetModelComparison.lean)
- [Compactification/TargetModelDiagram](Compactification/TargetModelDiagram.lean)
- [Compactification/ToDirectImageBaseChange](Compactification/ToDirectImageBaseChange.lean)
- [Compactification/ToTargetAlgebra](Compactification/ToTargetAlgebra.lean)
- [Compactification/ToTargetWhole](Compactification/ToTargetWhole.lean)
- [Open/ModuleLowerShriekValuedAdjunction](Open/ModuleLowerShriekValuedAdjunction.lean)
- [Open/ModuleLowerShriekValuedUnit](Open/ModuleLowerShriekValuedUnit.lean)
- [Open/ModuleScalarRestrictionAdjunction](Open/ModuleScalarRestrictionAdjunction.lean)
- [Open/ModuleScalarRestrictionDerived](Open/ModuleScalarRestrictionDerived.lean)
- [Open/ModuleScalarRestrictionLowerMate](Open/ModuleScalarRestrictionLowerMate.lean)
- [Open/ModuleScalarRestrictionRealization](Open/ModuleScalarRestrictionRealization.lean)
- [Open/ModuleScalarRestrictionSliceMate](Open/ModuleScalarRestrictionSliceMate.lean)
- [Open/ModuleScalarRestrictionValuedAdjunction](Open/ModuleScalarRestrictionValuedAdjunction.lean)
- [Open/ModuleScalarRestrictionValuedMate](Open/ModuleScalarRestrictionValuedMate.lean)
- [Open/ModuleScalarRestrictionValuedUnit](Open/ModuleScalarRestrictionValuedUnit.lean)
- [Open/ModuleStalkInside](Open/ModuleStalkInside.lean)
- [ProperOpen/Coherence](ProperOpen/Coherence.lean)
- [ProperOpen/Comparison](ProperOpen/Comparison.lean)
- [ProperOpen/Congruence](ProperOpen/Congruence.lean)
- [ProperOpen/HorizontalCoherence](ProperOpen/HorizontalCoherence.lean)
- [ProperOpen/Identity](ProperOpen/Identity.lean)
- [ProperOpen/MateNormalization](ProperOpen/MateNormalization.lean)
- [ProperOpen/Mate](ProperOpen/Mate.lean)
- [ProperOpen/RefinementRectangle](ProperOpen/RefinementRectangle.lean)
- [ProperOpen/RefinementTarget](ProperOpen/RefinementTarget.lean)
- [ProperOpen/ToDirectImageCompatibility](ProperOpen/ToDirectImageCompatibility.lean)
- [ProperOpen/ToDirectImageIdentity](ProperOpen/ToDirectImageIdentity.lean)
- [ProperOpen/ToDirectImageRefinementNaturality](ProperOpen/ToDirectImageRefinementNaturality.lean)
- [ProperOpen/ToDirectImageRefinement](ProperOpen/ToDirectImageRefinement.lean)
- [ProperOpen/ToDirectImageSquare](ProperOpen/ToDirectImageSquare.lean)
- [ProperOpen/ToDirectImage](ProperOpen/ToDirectImage.lean)
- [ProperOpen/TorsionCoherence](ProperOpen/TorsionCoherence.lean)
- [ProperOpen/VerticalPasting](ProperOpen/VerticalPasting.lean)
- [Unbounded/ArrowComparisonCoherence](Unbounded/ArrowComparisonCoherence.lean)
- [Unbounded/BaseChangeCompositionOriginal](Unbounded/BaseChangeCompositionOriginal.lean)
- [Unbounded/BaseChangeComposition](Unbounded/BaseChangeComposition.lean)
- [Unbounded/BaseIdentityModel](Unbounded/BaseIdentityModel.lean)
- [Unbounded/BaseModelIdentityCoherence](Unbounded/BaseModelIdentityCoherence.lean)
- [Unbounded/BaseModelSourceExchange](Unbounded/BaseModelSourceExchange.lean)
- [Unbounded/CartesianBaseChangeLiteral](Unbounded/CartesianBaseChangeLiteral.lean)
- [Unbounded/CartesianCompositionCanonical](Unbounded/CartesianCompositionCanonical.lean)
- [Unbounded/CartesianCompositionIdentity](Unbounded/CartesianCompositionIdentity.lean)
- [Unbounded/CartesianCompositionOpen](Unbounded/CartesianCompositionOpen.lean)
- [Unbounded/CartesianFirstCube](Unbounded/CartesianFirstCube.lean)
- [Unbounded/CartesianFirstHorizontal](Unbounded/CartesianFirstHorizontal.lean)
- [Unbounded/CartesianFirstNaturality](Unbounded/CartesianFirstNaturality.lean)
- [Unbounded/CartesianFirstRectangle](Unbounded/CartesianFirstRectangle.lean)
- [Unbounded/CartesianFirstStructural](Unbounded/CartesianFirstStructural.lean)
- [Unbounded/CartesianFirstTargetComparison](Unbounded/CartesianFirstTargetComparison.lean)
- [Unbounded/CartesianToDirectImageBaseChange](Unbounded/CartesianToDirectImageBaseChange.lean)
- [Unbounded/CartesianUnderlyingMap](Unbounded/CartesianUnderlyingMap.lean)
- [Unbounded/ChosenIdentityNormalization](Unbounded/ChosenIdentityNormalization.lean)
- [Unbounded/ChosenLeftUnitContraction](Unbounded/ChosenLeftUnitContraction.lean)
- [Unbounded/CoefficientCoproducts](Unbounded/CoefficientCoproducts.lean)
- [Unbounded/CompactificationBaseModel](Unbounded/CompactificationBaseModel.lean)
- [Unbounded/CompactifiedToDirectImageBaseChange](Unbounded/CompactifiedToDirectImageBaseChange.lean)
- [Unbounded/CompactifiedToDirectImageComposition](Unbounded/CompactifiedToDirectImageComposition.lean)
- [Unbounded/CompositionArrowComparison](Unbounded/CompositionArrowComparison.lean)
- [Unbounded/CompositionAssociativity](Unbounded/CompositionAssociativity.lean)
- [Unbounded/CompositionBCIdentity](Unbounded/CompositionBCIdentity.lean)
- [Unbounded/CompositionBCModelComparison](Unbounded/CompositionBCModelComparison.lean)
- [Unbounded/CompositionBCModelSquare](Unbounded/CompositionBCModelSquare.lean)
- [Unbounded/CompositionBCNormalization](Unbounded/CompositionBCNormalization.lean)
- [Unbounded/CompositionBCRawSource](Unbounded/CompositionBCRawSource.lean)
- [Unbounded/CompositionBCRefinementRaw](Unbounded/CompositionBCRefinementRaw.lean)
- [Unbounded/CompositionBCRefinement](Unbounded/CompositionBCRefinement.lean)
- [Unbounded/CompositionBCUnit](Unbounded/CompositionBCUnit.lean)
- [Unbounded/CompositionBaseChangeChosenModel](Unbounded/CompositionBaseChangeChosenModel.lean)
- [Unbounded/CompositionBaseChangeCube](Unbounded/CompositionBaseChangeCube.lean)
- [Unbounded/CompositionBaseChangeExchange](Unbounded/CompositionBaseChangeExchange.lean)
- [Unbounded/CompositionBaseChangeModel](Unbounded/CompositionBaseChangeModel.lean)
- [Unbounded/CompositionBaseChangePasting](Unbounded/CompositionBaseChangePasting.lean)
- [Unbounded/CompositionFamilyComparison](Unbounded/CompositionFamilyComparison.lean)
- [Unbounded/CompositionHorizontalPasting](Unbounded/CompositionHorizontalPasting.lean)
- [Unbounded/CompositionInterchange](Unbounded/CompositionInterchange.lean)
- [Unbounded/CompositionLeftUnitExpansion](Unbounded/CompositionLeftUnitExpansion.lean)
- [Unbounded/CompositionLeftUnitFace](Unbounded/CompositionLeftUnitFace.lean)
- [Unbounded/CompositionLeftUnitImage](Unbounded/CompositionLeftUnitImage.lean)
- [Unbounded/CompositionLeftUnitSource](Unbounded/CompositionLeftUnitSource.lean)
- [Unbounded/CompositionLeftUnitTransport](Unbounded/CompositionLeftUnitTransport.lean)
- [Unbounded/CompositionLeftUnit](Unbounded/CompositionLeftUnit.lean)
- [Unbounded/CompositionMixedRefinementFaces](Unbounded/CompositionMixedRefinementFaces.lean)
- [Unbounded/CompositionMixedRefinementWhole](Unbounded/CompositionMixedRefinementWhole.lean)
- [Unbounded/CompositionModelComparison](Unbounded/CompositionModelComparison.lean)
- [Unbounded/CompositionModelMaps](Unbounded/CompositionModelMaps.lean)
- [Unbounded/CompositionModel](Unbounded/CompositionModel.lean)
- [Unbounded/CompositionRawSquare](Unbounded/CompositionRawSquare.lean)
- [Unbounded/CompositionRefinementCube](Unbounded/CompositionRefinementCube.lean)
- [Unbounded/CompositionRefinementDirectImage](Unbounded/CompositionRefinementDirectImage.lean)
- [Unbounded/CompositionRefinementFaces](Unbounded/CompositionRefinementFaces.lean)
- [Unbounded/CompositionRefinementHorizontal](Unbounded/CompositionRefinementHorizontal.lean)
- [Unbounded/CompositionRightUnit](Unbounded/CompositionRightUnit.lean)
- [Unbounded/CompositionSingleModelFormulaBoundary](Unbounded/CompositionSingleModelFormulaBoundary.lean)
- [Unbounded/CompositionSingleModelFormula](Unbounded/CompositionSingleModelFormula.lean)
- [Unbounded/CompositionSingleModel](Unbounded/CompositionSingleModel.lean)
- [Unbounded/CompositionSingleSource](Unbounded/CompositionSingleSource.lean)
- [Unbounded/CompositionSingleTarget](Unbounded/CompositionSingleTarget.lean)
- [Unbounded/CompositionTripleInterchange](Unbounded/CompositionTripleInterchange.lean)
- [Unbounded/Composition](Unbounded/Composition.lean)
- [Unbounded/DirectImageCartesianFactor](Unbounded/DirectImageCartesianFactor.lean)
- [Unbounded/DirectImageContraction](Unbounded/DirectImageContraction.lean)
- [Unbounded/DirectImageSourceTransport](Unbounded/DirectImageSourceTransport.lean)
- [Unbounded/DirectImageSquare](Unbounded/DirectImageSquare.lean)
- [Unbounded/DirectImageStructuralSquare](Unbounded/DirectImageStructuralSquare.lean)
- [Unbounded/ExceptionalBaseModelIdentity](Unbounded/ExceptionalBaseModelIdentity.lean)
- [Unbounded/ExceptionalCoproducts](Unbounded/ExceptionalCoproducts.lean)
- [Unbounded/FamilyModelComparison](Unbounded/FamilyModelComparison.lean)
- [Unbounded/IdentityAmbientComparison](Unbounded/IdentityAmbientComparison.lean)
- [Unbounded/Identity](Unbounded/Identity.lean)
- [Unbounded/LeftUnitSourceExpansion](Unbounded/LeftUnitSourceExpansion.lean)
- [Unbounded/LeftUnitSourceRestriction](Unbounded/LeftUnitSourceRestriction.lean)
- [Unbounded/LeftUnitSuppliedIso](Unbounded/LeftUnitSuppliedIso.lean)
- [Unbounded/LeftUnitSupplied](Unbounded/LeftUnitSupplied.lean)
- [Unbounded/LeftUnitTotalComparison](Unbounded/LeftUnitTotalComparison.lean)
- [Unbounded/LocalizationComposition](Unbounded/LocalizationComposition.lean)
- [Unbounded/Localization](Unbounded/Localization.lean)
- [Unbounded/LowerShriekCoherence](Unbounded/LowerShriekCoherence.lean)
- [Unbounded/LowerShriekCompositionConjugacy](Unbounded/LowerShriekCompositionConjugacy.lean)
- [Unbounded/LowerShriekComposition](Unbounded/LowerShriekComposition.lean)
- [Unbounded/LowerShriekIdentityConjugacy](Unbounded/LowerShriekIdentityConjugacy.lean)
- [Unbounded/MixedToDirectImage](Unbounded/MixedToDirectImage.lean)
- [Unbounded/ModuleCoefficientCoproducts](Unbounded/ModuleCoefficientCoproducts.lean)
- [Unbounded/NormalizedBaseIdentityModel](Unbounded/NormalizedBaseIdentityModel.lean)
- [Unbounded/NormalizedToDirectImageBaseChange](Unbounded/NormalizedToDirectImageBaseChange.lean)
- [Unbounded/OpenBaseChangeIdentity](Unbounded/OpenBaseChangeIdentity.lean)
- [Unbounded/OpenComposition](Unbounded/OpenComposition.lean)
- [Unbounded/OpenIsomorphism](Unbounded/OpenIsomorphism.lean)
- [Unbounded/OpenNormalizationComparison](Unbounded/OpenNormalizationComparison.lean)
- [Unbounded/OpenNormalization](Unbounded/OpenNormalization.lean)
- [Unbounded/OpenToDirectImageBaseChange](Unbounded/OpenToDirectImageBaseChange.lean)
- [Unbounded/OpenToDirectImageComposition](Unbounded/OpenToDirectImageComposition.lean)
- [Unbounded/OpenToDirectImageIdentity](Unbounded/OpenToDirectImageIdentity.lean)
- [Unbounded/OpenToDirectImageOverComposition](Unbounded/OpenToDirectImageOverComposition.lean)
- [Unbounded/OpenToDirectImage](Unbounded/OpenToDirectImage.lean)
- [Unbounded/ProperAmplitude](Unbounded/ProperAmplitude.lean)
- [Unbounded/ProperCoproducts](Unbounded/ProperCoproducts.lean)
- [Unbounded/ProperNormalization](Unbounded/ProperNormalization.lean)
- [Unbounded/ProperOpenComparison](Unbounded/ProperOpenComparison.lean)
- [Unbounded/ProperOpenCongruence](Unbounded/ProperOpenCongruence.lean)
- [Unbounded/ProperOpenHorizontalCoherence](Unbounded/ProperOpenHorizontalCoherence.lean)
- [Unbounded/ProperOpenMateCoherence](Unbounded/ProperOpenMateCoherence.lean)
- [Unbounded/ProperOpenMateNormalization](Unbounded/ProperOpenMateNormalization.lean)
- [Unbounded/ProperOpenMate](Unbounded/ProperOpenMate.lean)
- [Unbounded/ProperOpenRefinementRectangle](Unbounded/ProperOpenRefinementRectangle.lean)
- [Unbounded/ProperOpenRefinementTarget](Unbounded/ProperOpenRefinementTarget.lean)
- [Unbounded/ProperOpenToDirectImage](Unbounded/ProperOpenToDirectImage.lean)
- [Unbounded/ProperOpenVerticalPasting](Unbounded/ProperOpenVerticalPasting.lean)
- [Unbounded/RawBaseIdentityModel](Unbounded/RawBaseIdentityModel.lean)
- [Unbounded/RawComparisonCongruence](Unbounded/RawComparisonCongruence.lean)
- [Unbounded/RawComparisonToDirectImage](Unbounded/RawComparisonToDirectImage.lean)
- [Unbounded/RawSourceIsoIdentity](Unbounded/RawSourceIsoIdentity.lean)
- [Unbounded/RawSourceToDirectImage](Unbounded/RawSourceToDirectImage.lean)
- [Unbounded/RawToDirectImageBaseChange](Unbounded/RawToDirectImageBaseChange.lean)
- [Unbounded/RawToDirectImage](Unbounded/RawToDirectImage.lean)
- [Unbounded/SourceIsoIdentity](Unbounded/SourceIsoIdentity.lean)
- [Unbounded/SourceIsoToDirectImage](Unbounded/SourceIsoToDirectImage.lean)
- [Unbounded/SuppliedComposition](Unbounded/SuppliedComposition.lean)
- [Unbounded/SuppliedToDirectImage](Unbounded/SuppliedToDirectImage.lean)
- [Unbounded/ToDirectImageBaseChange](Unbounded/ToDirectImageBaseChange.lean)
- [Unbounded/ToDirectImageCompositionModel](Unbounded/ToDirectImageCompositionModel.lean)
- [Unbounded/ToDirectImageComposition](Unbounded/ToDirectImageComposition.lean)
- [Unbounded/ToDirectImageNaturality](Unbounded/ToDirectImageNaturality.lean)
- [Unbounded/ToDirectImageRefinement](Unbounded/ToDirectImageRefinement.lean)
- [Unbounded/ToDirectImage](Unbounded/ToDirectImage.lean)
- [Unbounded/TripleCartesianComposition](Unbounded/TripleCartesianComposition.lean)
- [Unbounded/TripleCartesianLeftRoute](Unbounded/TripleCartesianLeftRoute.lean)
- [Unbounded/TripleCartesianMaps](Unbounded/TripleCartesianMaps.lean)
- [Unbounded/TripleCartesianRightRoute](Unbounded/TripleCartesianRightRoute.lean)
- [Unbounded/TripleChosenTotalComparison](Unbounded/TripleChosenTotalComparison.lean)
- [Unbounded/TripleHorizontalOpenTransport](Unbounded/TripleHorizontalOpenTransport.lean)
- [Unbounded/TripleOpenContraction](Unbounded/TripleOpenContraction.lean)
- [Unbounded/TripleRawComposition](Unbounded/TripleRawComposition.lean)
- [Unbounded/TripleSingleModelAssociativity](Unbounded/TripleSingleModelAssociativity.lean)
- [Unbounded/TripleSingleModelMaps](Unbounded/TripleSingleModelMaps.lean)
- [Unbounded/TripleSingleModels](Unbounded/TripleSingleModels.lean)
- [Unbounded/TripleTotalArrowComparison](Unbounded/TripleTotalArrowComparison.lean)
- [Unbounded/UnitIdentityValue](Unbounded/UnitIdentityValue.lean)
- [Unbounded/UnitModelArrow](Unbounded/UnitModelArrow.lean)
- [Unbounded/UnitModelComparison](Unbounded/UnitModelComparison.lean)
- [Unbounded/UnitModelCongruence](Unbounded/UnitModelCongruence.lean)
- [Unbounded/UnitModelFamily](Unbounded/UnitModelFamily.lean)
- [Unbounded/UnitModelRefinement](Unbounded/UnitModelRefinement.lean)
- [Unbounded/UnitModelSelf](Unbounded/UnitModelSelf.lean)
- [Unbounded/UnitModelToDirectImage](Unbounded/UnitModelToDirectImage.lean)
