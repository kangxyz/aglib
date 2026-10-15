# Cokernel pushouts and zero coproducts

The focused imports are `Aglib.CategoryTheory.Limits.Shapes.CokernelPushout` and `.ZeroObjects`. They retain the literal universal-property diagrams, rather than choosing replacement objects.

[CokernelPushout](CokernelPushout.lean) proves `CategoryTheory.Limits.isPushout_of_isColimit_cokernel`. In a preadditive category, a displayed cokernel cofork for `i` and `p`, an actual zero object `Z`, and the indicated arrows to and from `Z` give the pushout square with sides `i` and `p`. The cokernel universal property is an input; no abelian or monomorphism hypothesis is added.

[ZeroObjects](ZeroObjects.lean) proves `CategoryTheory.Limits.coprod_isZero`: a binary coproduct of two actual zero objects is zero. It requires a category with zero morphisms, existence of that binary coproduct and both zero-object proofs.

The [identity-cone functor](../../../Algebra/Homology/MappingCone/README.md) uses the cokernel pushout statement in its short-exactness comparison. The zero-coproduct statement supplies the lower primitive for [coproduct acyclicity of actual module-sheaf complexes](../../../AlgebraicGeometry/Modules/Complex/README.md). Neither leaf imports the application source from which its general statement was selected.
