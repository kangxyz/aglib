# The canonical site tensor bifunctor

[Basic](Basic.lean), imported as `Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Basic`, defines `SheafOfModulesOfCommRing.tensorLeftFunctor` and `tensorFunctor` as sheafification of the original presheaf tensor. Its maps are associated-sheaf images of the actual `tensorHom`, with original coefficient naturality.

The ambient data is a commutative-ring sheaf `R` on a site, with the stated `HasSheafCompose` for forgetting to ring sheaves, additive sheafification and equality of the sheafification weak equivalences with local bijectivity. Site object/morphism and coefficient universes remain explicit. `tensorLeftUnitIso` and `tensorBraiding` are the actual sheafified unit and braiding, with their original forward maps.

This leaf owns one construction. [Scheme tensors](../../../../../AlgebraicGeometry/Modules/Tensor/README.md) and [invertible-sheaf tensors](../../../../../AlgebraicGeometry/Modules/Invertible/README.md) delegate to it; [finite-free/retract properties](../README.md) provide separate exactness and injective-preservation results. No arbitrary-coefficient exactness is part of the tensor definition.
