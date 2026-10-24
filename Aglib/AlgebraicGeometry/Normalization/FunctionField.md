# Normalization in the original function field

For an integral scheme `W`, put

```text
γ = W.fromSpecStalk (genericPoint W)
N = γ.normalization
ν = γ.fromNormalization : N → W.
```

Mathlib's relative normalization supplies integral `N`, the integral and
affine original map `ν`, a dominant map `γ.toNormalization`, and the exact
factorization `γ.toNormalization ≫ ν = γ`.

`Scheme.genericNormalization_normalStalks` proves that `N` is normal.
For every nonempty affine open `U` of `W`, the original sections
`Γ(Spec K(W), γ⁻¹(U))` form a fraction ring of `Γ(W,U)`. The coefficient
compatibility is the original equation
`γ.app U ≫ (functionFieldSectionsIso W U).hom = W.germToFunctionField U`.
The actual ring `Γ(N,ν⁻¹(U))` is identified with its integral closure by
`normalizationObjIso`. This closure is normal, and localization gives
normality of each actual stalk of `N`.

`Scheme.genericInclusion_fieldMap_isIso` proves that the generic inclusion
induces an isomorphism on the original function fields. Flatness and
surjectivity on stalks make its actual generic stalk map invertible.
`Scheme.genericNormalization_isDominant` then uses the original
factorization. `Scheme.genericNormalization_fieldMap_isIso` cancels the
injective function-field map of `γ.toNormalization` to prove birationality
of the original `ν`.

`Scheme.genericNormalization_isFinite` assumes precisely that every
nonempty affine section ring `Γ(W,U)` is Nagata at auxiliary test universe
zero. The Nagata normalization theorem makes its literal integral closure
finite. `fromNormalization_app` and `normalizationObjIso` transfer that
finiteness to the actual section map of `ν`. The empty affine open is
handled through its zero-ring section map. No replacement normalization
object or existence of a finite model is assumed.

The [complementary-graph construction](../Surfaces/Resolution/ExtensionGraph/Construction.md)
takes `W` to be the actual schematic image of its original punctured
complementary section. It derives the chart Nagata properties from the
actual injective finite-type algebraic chart maps using
[FiniteTypeSurface](../../RingTheory/Nagata/FiniteTypeSurface.md).
For the complete-base corollary,
[CompleteLocalSurface](../../RingTheory/Nagata/CompleteLocalSurface.md)
supplies the initial Nagata property. These generic normalization results
alone do not assert H1 injectivity or construct a resolution.
