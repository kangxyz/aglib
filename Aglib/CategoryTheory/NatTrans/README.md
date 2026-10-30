# Natural transformations, units and exchange maps

[Unit](Unit.lean), imported as `Aglib.CategoryTheory.NatTrans.Unit`, owns `CategoryTheory.NatTrans.unitPostcompose`, `unitTotalPostcompose` and `unitPrecompose`. These are actual pre/postcomposition of a supplied natural unit; the component formula retains the original arrow and functor maps.

For `η : 𝟭 A ⟶ G` and `H : A ⥤ B`, `unitPostcompose_whiskerRight_app_of_eq` exposes the component of a transformation `τ : F ⋙ H ⟶ (G ⋙ F) ⋙ H` when an equality identifies `τ` with the stated whiskering. Its value is `H.map (F.map (η.app K))`, with the source and target objects fixed explicitly by the composite functor. The equality premise is part of this interface.

This is the single category-only implementation used by original scheme unit/Godement tensor wrappers. It does not assert that the supplied unit is invertible. Godement augmentation, total-image comparison and derived-unit equations are later consumers with their own boundedness or acyclicity premises.

The [Godement guide](../../AlgebraicGeometry/Cohomology/Godement/README.md) records these units' tensor and totalization specializations and the hypotheses of their quasi-isomorphism results.

[IsIsoOn](IsIsoOn.lean) records invertibility on an object property and restricts
the original transformation to an isomorphism with the same components.
[CompositeExchange](CompositeExchange.lean) pastes an original right exchange
with a specified left comparison.
[CompositeExchangeNaturality](CompositeExchangeNaturality.lean),
[NormalizedExchangeNaturality](NormalizedExchangeNaturality.lean) and
[OverComparisonEquation](OverComparisonEquation.lean) retain the actual
comparison, normalization and structural-compositor equations when transporting
naturality through that pasting.

[CartesianSourceExchange](CartesianSourceExchange.lean) transports a specified
exchange through an actual source comparison. Its component formula keeps the
original exchange, source comparison and inverse source compositor in that
order, and its model equation preserves the given comparison square. These
generic constructions retain independent categories and their original maps.
