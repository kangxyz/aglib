# The canonical site tensor bifunctor

[Basic](Basic.lean), imported as `Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Basic`, defines `SheafOfModulesOfCommRing.tensorLeftFunctor` and `tensorFunctor` as sheafification of the original presheaf tensor. Its maps are associated-sheaf images of the actual `tensorHom`, with original coefficient naturality.

The ambient data is a commutative-ring sheaf `R` on a site, with the stated `HasSheafCompose` for forgetting to ring sheaves, additive sheafification and equality of the sheafification weak equivalences with local bijectivity. Site object/morphism and coefficient universes remain explicit. `tensorLeftUnitIso` and `tensorBraiding` are the actual sheafified unit and braiding, with their original forward maps.

[RightUnit](RightUnit.lean), imported as `Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.RightUnit`, constructs `SheafOfModulesOfCommRing.tensorRightUnitIso`: tensoring with the structure module on the right is naturally isomorphic to the identity. `tensorRightUnitIso_hom_app` identifies the forward component with the associated-sheaf image of the actual presheaf right unitor followed by the module-sheafification counit. It retains the same sheafification hypotheses and independent coefficient/site universes. This leaf supplies the stated right-unit comparison and forward-map equation.

This family maintains one tensor construction. [Scheme tensors](../../../../../AlgebraicGeometry/Modules/Tensor/README.md) and [invertible-sheaf tensors](../../../../../AlgebraicGeometry/Modules/Invertible/README.md) delegate to it; [finite-free/retract properties](../README.md) provide separate exactness and injective-preservation results. No arbitrary-coefficient exactness is part of the tensor definition.

The right-unit leaf was integrated byte-for-byte from local Aglib revision `451aeda`; its existing delivered-Quillen provenance is preserved. Its dependency is the existing `Basic` leaf. No additional monoidal coherence assertion is supplied here.
