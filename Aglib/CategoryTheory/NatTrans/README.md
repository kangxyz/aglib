# Natural unit composition

[Unit](Unit.lean), imported as `Aglib.CategoryTheory.NatTrans.Unit`, owns `CategoryTheory.NatTrans.unitPostcompose`, `unitTotalPostcompose` and `unitPrecompose`. These are actual pre/postcomposition of a supplied natural unit; the component formula retains the original arrow and functor maps.

For `η : 𝟭 A ⟶ G` and `H : A ⥤ B`, `unitPostcompose_whiskerRight_app_of_eq` exposes the component of a transformation `τ : F ⋙ H ⟶ (G ⋙ F) ⋙ H` when an equality identifies `τ` with the stated whiskering. Its value is `H.map (F.map (η.app K))`, with the source and target objects fixed explicitly by the composite functor. The equality premise is part of this interface.

This is the single category-only implementation used by original scheme unit/Godement tensor wrappers. It does not assert that the supplied unit is invertible. Godement augmentation, total-image comparison and derived-unit equations are later consumers with their own boundedness or acyclicity premises.

The [Godement guide](../../AlgebraicGeometry/Cohomology/Godement/README.md) records these units' tensor and totalization specializations and the hypotheses of their quasi-isomorphism results.
