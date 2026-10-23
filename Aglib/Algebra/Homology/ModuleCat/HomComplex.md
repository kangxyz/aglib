# Native Hom cochains as a module-valued complex

[HomComplex.lean](HomComplex.lean) packages the existing
`CochainComplex.HomComplex.Cochain K L n` and `δ_hom R K L i j` in
`ModuleCat R`. The coefficient ring, original category and carrier universes
remain independent. The category is R-linear and preadditive; the
quasi-isomorphism result additionally assumes it is abelian and has the
specified native derived category.

`CochainComplex.HomComplex.moduleComplex R K L` uses these original cochains
and differential. `moduleComplexForgetIso` is the identity on cochains and
identifies its underlying additive complex with Mathlib's `HomComplex K L`.
`precomp` and `postcomp` use the original source and coefficient chain maps.
`moduleComplexFunctor` is the additive contravariant functor in the source
for a fixed coefficient complex.

For an actual quasi-isomorphism `f : K → L` and an actual K-injective target J,
`precomp_quasiIso` proves that

`moduleComplex R L J → moduleComplex R K J`

is a quasi-isomorphism. The proof describes the original map on cocycles and
cohomology classes, using `additivePrecompHomologyMapData`. The native
homotopy-to-derived comparison then identifies that exact map with
precomposition by `DerivedCategory.Q.map f`, which is an isomorphism.
Forgetting from modules to additive groups is used to reflect the
quasi-isomorphism of the already constructed R-linear chain map.

In the surface-duality application, specialize the original category to
`ModuleCat A` and the coefficient ring to A. A fixed injective R-resolution
of R is sent to the actual A-complex J by native scalar coinduction. The
passed exact-coinduction result and existing preservation of injectives
supply the augmentation and K-injectivity required here. The resulting Hom
complex is an actual A-module complex; an R-derived morphism commuting with
an A-action is not used as a replacement for an A-derived morphism.

This leaf supplies fixed-coefficient quasi-isomorphism invariance.
[Evaluation](HomComplex/Evaluation.md) constructs the original signed
A-linear evaluation, [Derived](HomComplex/Derived.md) localizes that same
map, and [Coinduction](HomComplex/Coinduction.md) retains its original
counit and double-evaluation square. [Perfect](HomComplex/Perfect.md)
proves invertibility of the genuine A-derived evaluation when the scalar
restriction has an actual bounded finite R-projective model and the
coefficient is the actual coinduced resolution of R. Surface concentration,
trace compatibility and the geometric Postnikov inputs remain separate.

Source basis: Aglib `8b93cc5940dc93f39a2eaf05e6985af28250a578`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1.
