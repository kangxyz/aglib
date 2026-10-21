# Formal functions on original cohomology

This family constructs the canonical comparison from
`AdicCompletion I (Sheaf.H (moduleAddSheaf X F) p)` to the compatible sections
of the original cohomology tower of `F / I^n F`, for a proper scheme over a
Noetherian affine base and an arbitrary coherent coefficient. It does not
assume relative flatness, completeness, or a projective embedding.

[QuotientTower](QuotientTower.lean) owns the actual inverse diagram, reduction
maps, connecting maps and their naturality, and scalar annihilation. Its
coefficient constructions are the original categorical images and cokernels
in [IdealPowers](../../Modules/IdealPowers/README.md).
[QuotientTowerBounds](QuotientTowerBounds.lean) performs the long-exact-sequence
argument: image estimates in degree p control reduction kernels, and shifted
kernel killing in degree p+1 controls transition ranges. Those estimates are
explicit inputs of these intermediate lemmas, not an unconditional proof of
formal functions.

[ReesFiniteness](ReesFiniteness.lean) applies the existing proper finiteness
theorem to the actual coherent image coefficient over the Rees algebra. The
coefficient is an image of a pullback unit, not the ordinary pullback itself
when the original coefficient is nonflat. [ReesCohomology](ReesCohomology.lean)
supplies the original Rees-linear comparison with the direct sum of ideal-power
cohomology, and [ReesCohomologyHomogeneous](ReesCohomologyHomogeneous.lean)
identifies its homogeneous action with the original ideal-power multiplication
maps. [Affine](Affine.lean) combines these suppliers with the adjacent-degree
bounds to prove the unconditional canonical formal-functions equivalence.
Its public statement has no additional Rees finiteness or stabilization premise.

The lower algebra suppliers are
[completion/tower comparison](../../../RingTheory/AdicCompletion/TowerComparison.lean)
and [graded Rees transitions](../../../RingTheory/ReesAlgebra/GradedTransition.lean).
They retain the original maps, independent universe parameters, and the
explicit hypotheses needed for their intermediate conclusions.

## Geometric Rees coefficient route

`ReesFiniteness.lean` applies proper coherent cohomology finiteness to the
actual geometric unit-image coefficient over the native Rees algebra.
`ReesLocalSections.lean`, `ReesLocalRestriction.lean`, and
`ReesLocalAction.lean` compare its affine sections with the direct sum of
the original ideal-power sections, preserving original restrictions and
multiplication. `ReesPresheafComparison.lean` extends this canonical affine
comparison to scalar-linear section sheaves; `ReesPresheafAction.lean`
retains the actual homogeneous coefficient square globally.

The reusable `ReesSections.lean` and `ReesPushforwardSections.lean` lower
bridges concern affine-basis extension and original pushforward sections,
respectively. These section comparisons do not identify the Rees image with
its tensor source and require no flatness assumption. Finite generation of
ideal-power cohomology requires the downstream original cohomology and
structural-action comparisons, not geometric finiteness alone.

[ThickeningCohomology](ThickeningCohomology.lean) compares each quotient stage
with original cohomology on the actual ideal thickening through the original
coefficient isomorphism and affine pushforward map. Its naturality uses the
actual geometric transition arrow. [ThickeningTower](ThickeningTower.lean)
packages that original diagram, its natural isomorphism, and its coordinatewise
compatible-family equivalence, including the zero stage.
[Thickening](Thickening.lean) composes this comparison with affine formal
functions. Its original-class coordinate is actual geometric pullback.

[CompleteBase](CompleteBase.lean) uses proper cohomology finiteness and
finite-module adic completeness, with independent module universes, to identify
original cohomology with the quotient and geometric thickening towers over a
complete Noetherian ring.
[LocalQuotientEquiv](LocalQuotientEquiv.lean) owns
`moduleHigherDirectImageStalkFormalFunctionsQuotientEquiv`, completing the
canonical identification of the actual higher-image stalk with cohomology over
the local spectrum. [LocalThickeningEquiv](LocalThickeningEquiv.lean) owns
`moduleHigherDirectImageStalkFormalFunctionsEquiv`, whose target is the native
compatible-family module of actual infinitesimal-fibre cohomology.
[Local](Local.lean) exports both equivalences and proves their `_of` coordinate
laws on original stalk classes. The base scheme need only be locally Noetherian;
no global Noetherian or separated hypothesis on it is added, and the local ideal
is arbitrary. No stalk/inverse-limit interchange or nonflat cohomology
base-change isomorphism is asserted.

[ThickeningSections](ThickeningSections.lean) compares the original quotient
families with the proper geometric tower at variable schemes and rings.
[ThickeningSectionsReduction](ThickeningSectionsReduction.lean) proves the
original reduction-to-geometric-pullback coordinate law before local
specialization. These preserve the original scalar structures and maps rather
than introducing an alternative limit model.

`ThickeningCohomologyComparison` proves the native bundled cohomology-map and
affine coefficient comparisons at variable schemes before geometric specialization.

[FibreFormalFunctions](../Proper/FibreFormalFunctions.lean) uses the canonical
geometric degree-zero tower to put every idempotent on an actual ideal
thickening in the image of restriction from original global functions. The
base is any Noetherian commutative ring, the morphism is proper, and the ideal
is arbitrary. The preimage need not be idempotent. The focused
[ordinary-stalk specialization](../Proper/FibreFormalFunctions/Stalk.lean)
puts every idempotent of a literal fibre in the image of the canonical ordinary
pushforward-stalk map for a proper morphism over a locally Noetherian target.
It retains the original germ and local-fibre restriction comparisons. Neither
image theorem assumes flatness, Henselianity, completeness, Grothendieck
existence, Artin approximation or object effectivity.
