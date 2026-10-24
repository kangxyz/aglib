# Finite-source affine closed-adjoint homology

`FiniteSource.lean` treats the original closed immersion
`Spec (R ⧸ I) → Spec R` for an arbitrary ideal `I` of a Noetherian
commutative ring. The coefficient `L` is an actual quasicoherent module
sheaf, and `J` is its supplied injective resolution. The complex
`closedImmersionRightAdjointQuotientResolutionComplex I J` is the actual
closed right adjoint applied termwise to `J.cochainComplex`.

The public interfaces are in `AlgebraicGeometry.Scheme.Modules`.

| Interface | Conditions and conclusion |
| --- | --- |
| `closedImmersionQuotientLocalizationHomologyMap_isLocalized` | The existing original geometric map localizes in every integer degree at the image of an ambient element. |
| `closedImmersionRightAdjointQuotientResolutionPrincipalSections_isLocalized` | The original section restriction localizes homology on every principal open of the quotient spectrum. |
| `closedImmersionRightAdjointQuotientResolutionTildeCounit_quasiIso` | The actual tilde-global-sections counit is a quasi-isomorphism. |
| `closedImmersionRightAdjointQuotientResolutionHomologyIso` and `_hom` | Exact tilde computes the original homology sheaf; the forward map is the inverse exact-tilde homology comparison followed by homology of the actual counit. |
| `closedImmersionRightAdjointQuotientResolutionHomology_quasicoherent` | Every homology sheaf is quasicoherent. |
| `closedImmersionRightAdjointQuotientResolutionHomology_isZero_of_neg` | Negative homology vanishes without Noetherianity or quasicoherence assumptions. |
| `closedImmersionRightAdjointQuotientResolutionSectionsHomology_finite` | Finite ambient global sections of `L` imply finite quotient-module homology of the original section complex. |
| `closedImmersionRightAdjointQuotientResolutionHomology_finite` and `_affineFiniteSheaf` | Under the same finite coefficient condition, homology has finite global sections and satisfies the existing affine coherent-sheaf predicate. |
| `closedImmersionRightAdjointQuotientResolutionHomology_finitePresentation` | The coherent homology has the existing sheaf finite-presentation property. |
| `closedImmersionRightAdjointQuotientResolutionHomology_finitePresentation_of_coefficient` | A finitely presented ambient coefficient supplies the finite-section hypothesis. |

For nonnegative degrees, the proof uses
`affineClosedRightAdjointResolutionExtLinearEquiv`, the original
`closedImmersionQuotientLocalizationHomologyMap_ext` equation, and
`ModuleCat.extScalarExtension_isLocalized_of_finite`. Thus the source
quotient isomorphism, coefficient comparison and exact-functor Ext map
remain those of the existing localization construction. Scalar restriction
transports ambient localization to localization over the quotient. For
negative degrees, the actual nonnegative injective resolution and the
additive right adjoint give zero terms and zero homology. The principal-open
section comparison retains the original restriction arrow and the original
`closedImmersionRightAdjointOpenIso`.

The principal-basis criterion then applies to the actual counit. Coherence
uses native `ModuleCat.finite_ext` only after finite global sections of the
coefficient have been supplied; it is independent of any concentration
argument. No regular sequence, coefficient frame, Gorenstein condition,
Cohen--Macaulay condition, or quasicoherence of injective terms is assumed.

The intended consumer is the affine coherence step of chosen-embedding
surface duality. This module does not supply a stalk-Ext identification,
transport from an arbitrary displayed affine surjection to its quotient,
geometric concentration, or trace compatibility. Those consumers must keep
their actual maps and their separate hypotheses.

Source correspondence: the general public localization interfaces and the
original section-to-counit assembly are in
[RegularList/Sheaf/Localization.lean](RegularList/Sheaf/Localization.lean) and
[RegularList/Sheaf/Counit.lean](RegularList/Sheaf/Counit.lean).
The new all-degree input is
[ModuleCat/Ext/Localization.lean](../../../../Algebra/Category/ModuleCat/Ext/Localization.lean).
