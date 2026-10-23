# Principal-open sections on qcqs schemes

`QCQSSections.lean` extends actual section localization from affine opens and
quasi-compact open subschemes of affine schemes to arbitrary quasi-compact
quasi-separated morphisms into an affine scheme. The coefficient is an actual
quasicoherent module sheaf. No finite generation, Noetherianity, local freeness,
trivialization or line-bundle hypothesis is imposed.

The source correspondence is the global-function specialization of [Stacks
28.18.2, tag 01PW](https://stacks.math.columbia.edu/tag/01PW), inspected on
2026-10-23. The native proof uses existing direct-image quasicoherence and affine
module localization, rather than repeating the finite-cover denominator proof.

## Original affine-base morphism

In `AlgebraicGeometry.Scheme.Modules.QuasiCoherent`,
`quasicoherent_pushforward_of_qcqs` proves quasicoherence of the actual ordinary
pushforward along a morphism `q` with `QuasiCompact q` and `QuasiSeparated q`.
It transports the degree-zero instance of the existing theorem
`Scheme.Cohomology.moduleHigherDirectImage_isQuasicoherent` through the canonical
`(Scheme.Modules.pushforward q).rightDerivedZeroIsoSelf`. Quasicoherence of the
ordinary pushforward is a conclusion, not an assumed oracle.

In the nested namespace `QCQSSections`, `isLocalizing_pushforward` applies this
result to `q : X ⟶ Spec A`. It proves localization for the original restriction
maps of the actual pushforward on every `PrimeSpectrum.basicOpen f`.

`exists_pow_smul_extension` takes an actual section `s` of that pushforward on
`D(f)` and produces `n : ℕ` and a section `t` over the whole affine base with

```text
restriction(t) = f^n • s.
```

Pushforward sections are definitionally sections of the original module on the
corresponding inverse-image opens. Thus this is an extension on `X`, including
when `q` is neither an open immersion nor an affine morphism. The scalar action
is the original structural `A`-action on those sections.

`exists_pow_smul_eq_zero` supplies the matching annihilation statement: a global
section restricting to zero on the inverse image of `D(f)` is killed by a power
of the same original `f`.

## Original global function

For a scheme `X` with `CompactSpace X` and `QuasiSeparatedSpace X`, the canonical
map `X.toSpecΓ` has the required morphism instances. The theorem
`QCQSSections.toSpecΓ_smul` explicitly compares the base-ring action on its
pushforward sections with multiplication by the restriction of the original
global function on `X`.

`QCQSSections.exists_power_mul_eq_restriction` therefore has the direct endpoint:
for an actual quasicoherent `M : X.Modules`, `f : Γ(X, ⊤)` and
`s : Γ(M, X.basicOpen f)`, there are `n : ℕ` and `t : Γ(M, ⊤)` whose literal
restriction to `X.basicOpen f` equals the `n`th power of the literal restriction
of `f`, acting on `s`. The proof transports along the exact equality
`X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f`; it does not replace a
module section by a function.

## Relationship to existing leaves

`AffineOpenSections` proves the lower affine-open extension and annihilation
statements. `AffineSectionsQuasicoherent` proves the version for a quasi-compact
open immersion into an affine scheme. `AffineSectionsGlobal` transports that
open-immersion quasicoherence result to arbitrary targets. None has the arbitrary
qcqs morphism hypothesis used here, so these existing implementations are left
unchanged.

The precise new dependency is the existing
`Cohomology.DirectImage.QuasiCoherent` leaf, together with Mathlib's actual affine
module localization and qcqs morphism interfaces. This leaf does not import any
contraction, nonvanishing-section or ampleness construction. A current consumer
is the principal-base-denominator step in the corrected quasi-projective
exceptional-curve contraction argument.

The parent family README and import facades are maintained separately by the
principal. Compiler validation is coordinated by the principal on the assigned
remote batch; this source delivery alone asserts no compilation or review result.
