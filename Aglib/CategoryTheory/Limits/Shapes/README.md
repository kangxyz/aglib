# Cokernel pushouts and zero coproducts

The focused imports are `Aglib.CategoryTheory.Limits.Shapes.CokernelPushout` and `.ZeroObjects`. They retain the literal universal-property diagrams, rather than choosing replacement objects.

[CokernelPushout](CokernelPushout.lean) proves `CategoryTheory.Limits.isPushout_of_isColimit_cokernel`. In a preadditive category, a displayed cokernel cofork for `i` and `p`, an actual zero object `Z`, and the indicated arrows to and from `Z` give the pushout square with sides `i` and `p`. The cokernel universal property is an input; no abelian or monomorphism hypothesis is added.

[ZeroObjects](ZeroObjects.lean) proves `CategoryTheory.Limits.coprod_isZero`: a binary coproduct of two actual zero objects is zero. It requires a category with zero morphisms, existence of that binary coproduct and both zero-object proofs.

The [identity-cone functor](../../../Algebra/Homology/MappingCone/README.md) uses the cokernel pushout statement in its short-exactness comparison. The zero-coproduct statement supplies the lower primitive for [coproduct acyclicity of actual module-sheaf complexes](../../../AlgebraicGeometry/Modules/Complex/README.md). Neither leaf imports the application source from which its general statement was selected.

[SequentialSystem](SequentialSystem/README.md) owns the natural-number indexing shape: explicit colimit comparisons for invertible successor maps, finite-tail comparisons, eventual invertibility of the original colimit legs, and alternating-sign correction of stage morphisms. These are separate from the finite cokernel and coproduct shapes above; general colimit comparisons need no additive structure, while sign correction requires a preadditive category.

[BinaryProducts](BinaryProducts.lean) gives the product-preserving-functor criterion for a
mapped morphism into a binary product to vanish when both mapped projections vanish.

[RegularKernel](RegularKernel.lean) proves
`preservesKernel_of_generalizedInverse`. An actual morphism `f` with a
displayed generalized inverse `s`, satisfying `f ≫ s ≫ f = f`, has its
kernel preserved by every additive functor between preadditive categories.
Only existence of that one source kernel is required. Its complementary
projection is the original `1 - f ≫ s`; no abelian or exact-functor
hypothesis is introduced.

`kernelRetractOfGeneralizedInverse` exposes the actual kernel retract and
its complementary projection, while `sourceRetractOfGeneralizedInverse`
expresses the source as a retract of the kernel plus the target. The
kernel-preservation proof uses this same implementation. These actual
retractions also supply the projectivity criterion in the abelian family.

[WidePullbacks](WidePullbacks.lean) proves
`CategoryTheory.Limits.WidePullback.exists_lift_base_iff`: a morphism to the
base factors through the wide pullback of a family of arrows if and only if it
factors through every member, and `WidePullback.mono_base`: the base of a wide
pullback of monomorphisms is a monomorphism. Only existence of the wide
pullback is assumed. The consumer is the joint rank stratification of the
[flattening stratification](../../../AlgebraicGeometry/FlatteningStratification/README.md).
