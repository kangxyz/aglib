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

The first leaf passed alone through the shared guarded wrapper with receipt
`1792109940210200000-46840`. [Descent](Descent.lean) and
[CoherentSupport](CoherentSupport.lean) supply the killed-image and coherent
thickening interfaces described below. The ordinary
closed right adjoint is owned by the shared duality workstream; this family
does not introduce another implementation of it.

The external arbitrary-universe `ClosedImmersionKilledConsumer.lean` passed
with receipt `1792110030546577000-48070`. It checks the original section and
stalk formulas without quasicoherence or finiteness assumptions. All seven
inspected public theorems use only `propext`, `Classical.choice` and
`Quot.sound`.

`Stalk` identifies both original geometric adjunction maps with the native
scalar-extension maps through the original stalk isomorphisms.
`pullbackPushforwardUnit_moduleStalk` and
`pullbackPushforwardCounit_moduleStalk` apply to inducing scheme maps.
`pullbackPushforwardCounit_isIso_of_closedImmersion` uses the actual
surjective stalk ring maps to prove the original counit invertible on
every module sheaf. `fullyFaithfulPushforwardOfClosedImmersion` therefore
provides all-module full faithfulness of the original closed pushforward.
This leaf passed with receipt `1792110689834166000-59282`, under the default
budget. No quasicoherence or Noetherianity is imposed.

The independent `ClosedImmersionStalkCounitConsumer.lean` passed with
receipt `1792110782416699000-60694`; its four original unit, counit and
full-faithfulness interfaces use only the three standard axioms.

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

The locality source passed with receipt `1792111142483226000-66837` at the
default budget. Its independent `ClosedImmersionLocalityConsumer.lean`
passed with receipt `1792111566228725000-73753`, checking the actual section,
germ, support and stalk interfaces. All five inspected declarations use
only the three standard axioms.

`Descent` proves
`pullbackPushforwardUnit_isIso_iff_killedByIdealSheaf` and
`mem_essImage_pushforward_iff_killedByIdealSheaf` for every closed immersion
and every actual target module sheaf. `closedImmersionDescentIso` uses the
actual ordinary pullback as its descended coefficient and the inverse of
the original geometric adjunction unit as its comparison. Its inverse is
literally that unit, and original coefficient maps commute with the
comparison. No quasicoherence, finite generation or Noetherianity is
required. The original stalk-unit criterion is public as well.

The descent source passed with receipt `1792111860478362000-77417` in
2.4 seconds under the default budget. Its independent
`ClosedImmersionDescentConsumer.lean` passed with receipt
`1792111892180610000-77617`, including a literal-unit check and actual
coefficient naturality. All six inspected declarations use only the three
standard axioms. Coherent support-power descent will specialize this same
ordinary all-module interface.

`Support` first compares original sheaf stalk support with native support
of the actual section module on every affine open. Consequently finite
actual sections supported in `I.support` are annihilated by a positive
power of the original ideal `I.ideal U`, provided that ideal is finitely
generated. The sheaf is quasicoherent; neither the ring nor the scheme is
assumed Noetherian for these affine statements. The section action is
transported through the original affine-chart restriction unit.

This affine support source passed with receipt `1792112875002826000-90557`
in 2.8 seconds. `ClosedImmersionAffineSupportConsumer.lean` passed with
receipt `1792112909854241000-90959`; both public declarations use only the
three standard axioms. Finite-cover uniformization and direct thickening
descent use these actual affine powers.

The uniform `Support` interface is now proved:
`killedByIdealSheaf_of_affineCover` patches original affine-section
annihilation over any actual affine cover, using the native ideal
restriction equality and the lower quasicoherent annihilator comparison.
`exists_pos_pow_killedByIdealSheaf_of_support_subset` then takes one
positive maximum exponent over a finite affine subcover. Its exact inputs
are compactness of the scheme, quasicoherence, finite actual section
modules on affine opens and finite generation of the actual chart ideals.
No Noetherian hypothesis is hidden in this general statement.

The completed uniformization source passed with receipt
`1792113194620766000-94745` in 3.2 seconds. The refreshed independent
`ClosedImmersionAffineSupportConsumer.lean` passed with receipt
`1792113264905191000-95764`, including an independent cover-index universe;
all four inspected declarations use only the three standard axioms.

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

The source passed with receipt `1792113495879079000-99987` in 2.3 seconds
at the default budget. `CoherentThickeningDescentConsumer.lean` passed with
receipt `1792113580563646000-1704`, checking actual ordinary pullback,
coherence, positive thickening, exact image and the literal original unit.
Both new inspected declarations use only the three standard axioms.

[RightAdjoint](RightAdjoint.lean) constructs the ordinary right adjoint of the
actual closed pushforward on all module sheaves. The native special adjoint
functor theorem uses the proved all-small-colimit preservation and the native
Grothendieck category's separator and size properties. The single chosen
`closedImmersionRightAdjoint` comes with `closedImmersionRightAdjunction`,
additivity, limit preservation and preservation of injective objects. These
statements impose no quasicoherence, Noetherianity or finiteness hypothesis.
[RightAdjoint/Affine](RightAdjoint/Affine.lean) now proves its actual affine
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
