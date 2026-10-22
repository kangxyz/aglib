# Actual closed-immersion module interfaces

Import `Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Killed`.
`Scheme.Modules.killedByIdealSheaf I` is an object property on the actual
category `X.Modules`: every original affine ideal `I.ideal U` annihilates
the original sections of the coefficient on `U`. It has no quasicoherence,
finite-type, flatness or Noetherian hypothesis. It is invariant under actual
module isomorphisms and is antitone in the ideal.

`killedByIdealSheaf_pushforward_ker f M` proves that every actual pushforward
is killed by the native scheme-map kernel ideal. This statement holds for
every scheme morphism, since the native ideal lies in each actual section
ring-map kernel.

`pushforwardModuleStalkIso_smul` retains the actual scalar action through
the native inducing-map stalk comparison. The associated
`pushforward_stalk_smul_eq_zero_of_isInducing` and
`closedImmersion_pushforward_stalk_smul_eq_zero` identify annihilation by
the kernel of the original stalk ring map, for arbitrary coefficient
module sheaves. The scalar formulas keep the original restricted carriers
and original comparison map.

`Stalk` identifies both original geometric adjunction maps with the native
scalar-extension maps through the original stalk isomorphisms.
`pullbackPushforwardUnit_moduleStalk` and
`pullbackPushforwardCounit_moduleStalk` apply to inducing scheme maps.
`pullbackPushforwardCounit_isIso_of_closedImmersion` uses the actual
surjective stalk ring maps to prove the original counit invertible on
every module sheaf. `fullyFaithfulPushforwardOfClosedImmersion` therefore
provides all-module full faithfulness of the original closed pushforward.
No quasicoherence or Noetherianity is imposed.

Full faithfulness here concerns the ordinary module categories. Even
though closed pushforward is exact, its induced derived functor need not
be fully faithful. Similarly, modules annihilated by an ideal form the
quotient-module essential image, whose inclusion need not be closed under
extensions: an extension of two modules killed by `I` can require `I²`.
No derived full faithfulness or Serre property of this image is asserted.

`Locality` detects the same affine annihilation condition on original germs
and actual module stalks. It proves that an arbitrary annihilated module
vanishes off the native ideal support. For an inducing quasi-compact map,
every element of the original stalk ring-map kernel has an affine
representative in the native kernel ideal. Consequently affine kernel-ideal
annihilation implies annihilation by the original stalk-map kernel.
These statements impose no quasicoherence or finite-type hypothesis.

`Descent` proves
`pullbackPushforwardUnit_isIso_iff_killedByIdealSheaf` and
`mem_essImage_pushforward_iff_killedByIdealSheaf` for every closed immersion
and every actual target module sheaf. `closedImmersionDescentIso` uses the
actual ordinary pullback as its descended coefficient and the inverse of
the original geometric adjunction unit as its comparison. Its inverse is
literally that unit, and original coefficient maps commute with the
comparison. No quasicoherence, finite generation or Noetherianity is
required. The original stalk-unit criterion is public as well.

`Support` first compares original sheaf stalk support with native support
of the actual section module on every affine open. Consequently finite
actual sections supported in `I.support` are annihilated by a positive
power of the original ideal `I.ideal U`, provided that ideal is finitely
generated. The sheaf is quasicoherent; neither the ring nor the scheme is
assumed Noetherian for these affine statements. The section action is
transported through the original affine-chart restriction unit.

`Support` also supplies the uniform interfaces:
`killedByIdealSheaf_of_affineCover` patches original affine-section
annihilation over any actual affine cover, using the native ideal
restriction equality and the lower quasicoherent annihilator comparison.
`exists_pos_pow_killedByIdealSheaf_of_support_subset` then takes one
positive maximum exponent over a finite affine subcover. Its exact inputs
are compactness of the scheme, quasicoherence, finite actual section
modules on affine opens and finite generation of the actual chart ideals.
No Noetherian hypothesis is hidden in this general statement.

`CoherentSupport` specializes the same support-power proof to a coherent
actual module on a Noetherian scheme. The Noetherian hypothesis supplies
compactness and finite generation of the actual chart ideals; coherence
supplies finite actual affine sections. `exists_coherent_thickening_descent`
constructs a positive exponent and descends directly to `(I ^ n).subscheme`
with coefficient the original ordinary pullback. Its original closed
pushforward is isomorphic to the unchanged module through the existing
inverse-unit descent comparison, and its closed image is exactly
`I.support`. Reducedness and full support of the coefficient are unnecessary.
No ideal-adic filtration or prime-filtration input is used.

[RightAdjoint](RightAdjoint.lean) constructs the ordinary right adjoint of the
actual closed pushforward on all module sheaves. The native special adjoint
functor theorem uses the proved all-small-colimit preservation and the native
Grothendieck category's separator and size properties. The single chosen
`closedImmersionRightAdjoint` comes with `closedImmersionRightAdjunction`,
additivity, limit preservation and preservation of injective objects. These
statements impose no quasicoherence, Noetherianity or finiteness hypothesis.
[RightAdjoint/Affine](RightAdjoint/Affine.lean) proves its actual affine
coinduction formula, S-linearity, original unit/counit and Hom-adjoint
compatibility for arbitrary target sheaves.
[RightAdjoint/Restriction](RightAdjoint/Restriction.lean) proves ordinary
open restriction with the original unit, counit and Hom-adjoint equations;
[native D+ restriction](../../Cohomology/ClosedImmersion/README.md) derives
that same comparison.
[Regular-list sheaf purity](../../Cohomology/ClosedImmersion/RightAdjoint/RegularList/Sheaf.lean)
computes the installed affine right adjoint for an ordered weakly regular
list and a quasicoherent ring-framed coefficient, retaining the original
Koszul class. [Canonical](../../Cohomology/Duality/Projective/Canonical.lean)
glues the determinant-normalized comparison for a closed immersion between
fixed-dimension smooth schemes over the same arbitrary base. General
coefficients in relative duality retain the actual right-adjoint object;
neither arbitrary-coefficient purity nor derived full faithfulness is asserted.

[QuotientComparison](QuotientComparison.lean) compares the original
pullback/pushforward quotients for closed immersions with equal native kernel
ideals. The comparison preserves their actual adjunction units and arbitrary
coefficient morphisms, without coherence or flatness hypotheses.

[Unit](Unit.lean) proves that the original pullback/pushforward unit for a
closed immersion is an epimorphism on every module sheaf. It uses the original
module-stalk comparison and surjectivity of the scalar extension unit, without
coherence or flatness assumptions. It supplies canonical formal quotient transitions.

[StructureQuotient](StructureQuotient.md) applies that same quotient unit to
the original structure-module map. `Hom.structureModuleMap_epi` and
`Hom.idealSequence_shortExact` give its actual short exact kernel sequence,
with the existing `Hom.idealModule` and `Hom.idealInclusion`. These statements
apply to every closed immersion without quasicoherence or finiteness conditions.

[Closed-pullback Nakayama detection](Nakayama.md) proves
`Scheme.Modules.epi_of_pullback_closedImmersion_of_stalkFinite` for an
original map `φ : M ⟶ N` and closed immersion `i : E ⟶ X`. It requires
epimorphy of the actual pulled map, finiteness of the original target stalks
at points in the image of `i`, and epimorphy of the original stalk maps off
that image.
The source module is arbitrary; quasicoherence, Noetherianity and flatness
are unnecessary. The `..._stalkSurjective` variant takes surjectivity of the
same off-image stalk maps. The
[Cartier neighborhood](../../Morphisms/Proper/CartierNeighborhood.md) and
[image-point ideal](../../Surfaces/Contraction/PointIdeal.md) consumers supply
these actual first-order, finite-target and complement hypotheses.

[KilledSubobject](KilledSubobject.lean) transfers actual affine ideal-sheaf
annihilation to ordinary monomorphic subobjects, using injectivity on the
original sections and no quasicoherence hypothesis.
