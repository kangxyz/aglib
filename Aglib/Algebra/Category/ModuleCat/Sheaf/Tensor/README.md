# The canonical site tensor bifunctor

[Basic](Basic.lean), imported as `Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Basic`, defines `SheafOfModulesOfCommRing.tensorLeftFunctor` and `tensorFunctor` as sheafification of the original presheaf tensor. Its maps are associated-sheaf images of the actual `tensorHom`, with original coefficient naturality.

The ambient data is a commutative-ring sheaf `R` on a site, with the stated `HasSheafCompose` for forgetting to ring sheaves, additive sheafification and equality of the sheafification weak equivalences with local bijectivity. Site object/morphism and coefficient universes remain explicit. `tensorLeftUnitIso` and `tensorBraiding` are the actual sheafified unit and braiding, with their original forward maps.

[RightUnit](RightUnit.lean), imported as `Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.RightUnit`, constructs `SheafOfModulesOfCommRing.tensorRightUnitIso`: tensoring with the structure module on the right is naturally isomorphic to the identity. `tensorRightUnitIso_hom_app` identifies the forward component with the associated-sheaf image of the actual presheaf right unitor followed by the module-sheafification counit. It retains the same sheafification hypotheses and independent coefficient/site universes. This leaf supplies the stated right-unit comparison and forward-map equation.

This family maintains one tensor construction. [Scheme tensors](../../../../../AlgebraicGeometry/Modules/Tensor/README.md) and [invertible-sheaf tensors](../../../../../AlgebraicGeometry/Modules/Invertible/README.md) delegate to it; [finite-free/retract properties](../README.md) provide separate exactness and injective-preservation results. No arbitrary-coefficient exactness is part of the tensor definition.

The right-unit leaf was integrated byte-for-byte from local Aglib revision `451aeda`; its existing delivered-Quillen provenance is preserved. Its dependency is the existing `Basic` leaf. 
[Monoidal/Objects](Monoidal/Objects.lean), [Associator](Monoidal/Associator.lean),
[Basic](Monoidal/Basic.lean) and [Symmetric](Monoidal/Symmetric.lean) descend
actual presheaf coherence to the chosen sheafified tensor, retaining the original
unitors, associator and braiding. This construction assumes monoidal stability
of the sheafification weak equivalences. Its current ring and module carriers
share one universe; site-object and site-morphism universes remain independent.
Scheme tensor coherence specializes these constructions.

[InternalHom/TensorAdjunction](../InternalHom/TensorAdjunction.lean) constructs
the actual right-tensor adjunction `Hom(M tensor N, P) ≃ Hom(M, Hom(N,P))`.
Its counit evaluates `Hom(N,P) tensor N`.
[Monoidal/Stability](Monoidal/Stability.lean) uses presheaf-source Hom and the
sheaf-target bijectivity criterion to prove the required stability, without
points or an assumed monoidal weak-equivalence class. These closed constructions
take ring and module carriers already in the explicit common universe
`max uC vC r`. Plain internal Hom retains its independent ring universe and
its natural output-size bound.
