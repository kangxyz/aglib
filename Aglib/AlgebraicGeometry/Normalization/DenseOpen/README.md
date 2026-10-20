# Dense-open and relative normalization

[DenseOpen](../DenseOpen.lean) proves `Scheme.denseOpenNormalNormalization`, a term of the
exact universal `Scheme.DenseOpenNormalNormalization` interface. Every qcqs dominant open
immersion into an integral scheme with `Scheme.NormalStalks` has an isomorphism as its actual
Mathlib `fromNormalization`. Schemes are arbitrary in one universe; no Noetherianity,
excellence, dimension bound or purity statement is required.

`Scheme.Hom.integralClosure_algebraMap_bijective_of_isOpenImmersion` is the affine input.
On each nonempty affine open, it embeds the source sections in the base function field using
the native open-immersion `FunctionField.fieldEquiv`. Normality of the actual target stalks
gives integral closedness of its affine sections. Thus the actual algebra map to the integral
closure is bijective. Mathlib's `fromNormalization_app` and locality of isomorphisms yield the
scheme theorem. Dominance supplies nonemptiness; source integrality is derived from the open
immersion. The affine input does not require qcqs.

`denseOpenNormalizationIso` is `asIso j.fromNormalization`; its forward map and both triangles
are exposed. It introduces no alternate normalization object. [Relative](../Relative.lean)
provides `Scheme.Hom.normalizationIntegralFactorIso`, `normalizationSourceIso`, their literal
structural and generic triangles, the given smooth-pullback comparison,
`normalizationDesc_isIso`, and étale descent along a supplied smooth, surjective,
quasi-compact base-change square. Their original hypotheses remain explicit.

The exact packet source is `R5Lab/Aglib/AlgebraicGeometry/Normalization/Relative.lean` at
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`650965d46d326d81575d6457010fa1de4322761ba02e99750e4ccb68df65bbbc`.
Its `RegularLocalDomainNormality` predicate denotes the universal expression
`∀ (A : Type u) [CommRing A] [IsDomain A] [IsRegularLocalRing A], IsIntegrallyClosed A`.
The existing native `IsRegularLocalRing.isIntegrallyClosed_of_regularLocal` supplies that
expression, including without the redundant domain assumption. No parallel scheme-level
ring predicate is introduced.

[DenseOpenNormalization](../../../../AglibTest/DenseOpenNormalization.lean) checks the exact
universal type, the literal maps and affine coefficient map, and use in the actual smooth-square
and integral-final-factor comparisons. Generic finite étale normalization continues to use
the existing [GenericFiniteEtale](../GenericFiniteEtale/README.md) objects and comparisons.
