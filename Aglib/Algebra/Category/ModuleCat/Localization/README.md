# Exactness through actual module localizations

Import `Aglib.Algebra.Category.ModuleCat.Localization.Exactness`; [Exactness](Exactness.lean) extends `ModuleCat` using actual categorical module diagrams.

`ModuleCat.isLocalizedModule_piMap` proves that a finite categorical product of supplied localization maps is a localization map. The finite product index and actual localized coefficient maps remain inputs.

`ModuleCat.shortComplex_exact_of_isLocalized_span` detects exactness of an actual module short complex from compatible localized short complexes. The localizing elements must span the unit ideal, and the localized complexes must be exact. It does not infer these premises from a merely chosen set of elements.

The consumers are [generic basis/sheaf exactness](../../../../Topology/Sheaves/README.md) and affine section/Cech arguments. The lower objects are native commutative-ring localizations and module short complexes; no finite-generation or geometric hypothesis is added beyond the source statement.

[Submodule](Submodule.lean) identifies when the actual localized inclusion of a submodule
is an isomorphism, through equality of its localized underlying submodule with the top.

[Homology](Homology.lean) treats an original natural transformation
`τ : 𝟭 (ModuleCat R) ⟶ F` to an additive homology-preserving endofunctor.
If each original component is a localization at `S`, then its native
short-complex homology map is a localization. The actual
`localizationComplexUnit` retains `τ` termwise and has a localizing
homology map in every complex shape and degree. Ring, module-carrier and
index universes remain independent. The proof uses native
`NatTrans.app_homology` and the original exact-functor homology
isomorphisms. Actual affine tilde section complexes consume this rule.

[ScalarExtension](ScalarExtension.lean) proves that the original native
extension/restriction adjunction unit is localizing when the specified
`σ.toAlgebra` exhibits the target as a localization. If an original
restricted module map has an invertible native scalar-adjunction mate,
`isLocalizedModule_of_isIso_adjoint` identifies that same map as a
localization. Ring universes are independent; the coefficient carrier is
the native `max m s` required by this scalar adjunction. Canonical qcqs
cohomology base change supplies an immediate geometric consumer.

[Projective](Projective.lean) identifies membership in the native free
locus with freeness of the actual scalar-extension object at a prime,
without a finite-presentation hypothesis. For a finitely presented module,
a basic open contained in that locus makes the original scalar extension
to the basic-open ring projective. The native localized-module/tensor and
scalar-extension/tensor comparisons retain the actual module objects.
This supplies the basic-open neighbourhood criterion for homology base
change.

[Counit](Counit.lean) uses the existing scalar-action comparison
`ModuleCat.extendScalarsAlgebraIso`. Its localization isomorphism has the original
`extendRestrictScalarsAdj` counit as its forward map, with the same unit-pure-tensor
formula. `restrictThenLocalizeIso` keeps the specified coefficient homomorphism.
[BaseChange](BaseChange.lean) supplies the natural isomorphism between literal tensor scalar
extension and the actual localized-module functor over an arbitrary commutative
base ring. Both leaves reuse the existing native scalar/tensor models.
