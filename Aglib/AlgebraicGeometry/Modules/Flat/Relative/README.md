# Relative flatness over the actual base stalks

Import `Aglib.AlgebraicGeometry.Modules.Flat.Relative` for
`Scheme.Modules.relativeFlat f M`. For each actual point `x : X`, this property
requires the original coefficient stalk `M_x` to be flat over the base local
ring `𝒪_(Y,f(x))`, using restriction of scalars along `f.stalkMap x`.
It imposes no quasicoherence or finiteness condition. This is distinct from
`stalkwiseFlat X M`, which tests flatness over `𝒪_(X,x)`.

`relativeTensorStalkIso` uses the original geometric pullback stalk comparison,
the original sheaf-tensor stalk comparison and the unchanged scalar-compatible
tensor isomorphism. After restriction to the base local ring, it identifies
pullback followed by tensor-right with tensor by the restricted coefficient
stalk. It retains the original coefficient maps through naturality.

`mono_pullback_tensorRight_of_relativeFlat` proves injective preservation for
the actual pullback-tensor functor; the corresponding native
`PreservesMonomorphisms` property is also provided. Neither affineness,
quasicoherence nor flatness of the scheme morphism is assumed.

The Relative leaf passed alone through the shared guarded wrapper, receipt
`1792090320042901000-93701`. The first-variable scalar tensor prerequisite
passed separately with receipt `1792090106587567000-87892`.
The external `work/proper-validation/RelativeFlatConsumer.lean` checks the
original base-stalk property, natural stalk comparison and actual monomorphism
conclusion, with receipt `1792090472141627000-98196`. The inspected proofs use
only `propext`, `Classical.choice` and `Quot.sound`.

`Aglib.AlgebraicGeometry.Modules.Flat.Relative.Locality` transports relative
flatness through actual coefficient isomorphisms and the original
open-restriction stalk isomorphism. The map to the base is composed with the
given open immersion; the base local ring stays the one at the original point.

Over `Spec A`, `flat_stalk_over_spec_of_relativeFlat` gives flatness of the
actual coefficient stalk over `A`. Its scalar map is the native structural
`StructureSheaf.toStalk` followed by the original morphism's `stalkMap`.
For `Spec.map φ`, `flat_stalk_of_relativeFlat_specMap` identifies this with
the literal action of `φ` followed by the source structural stalk map. The
proof uses native localization flatness of the base local ring; no
quasicoherence or flatness of `φ` is required for these stalk statements.
The Locality leaf passed separately with receipt `1792091002190712000-12041`.

Import `Aglib.AlgebraicGeometry.Modules.Flat.Relative.AffineSections` for
actual section flatness. For a given ring map `φ : A ⟶ B`,
`flat_moduleSpecΓFunctor_of_relativeFlat` proves `A`-flatness of the original
`moduleSpecΓFunctor.obj M`, restricted along `φ`, when `M` is quasicoherent
and relatively flat for `Spec.map φ`. Native maximal-ideal localization
detection uses the original `tilde.toStalk` maps. The original `fromTildeΓ`
isomorphism identifies their actual localized stalks with the coefficient
stalks already proved flat over `A`.

`flat_affineOpen_sections_of_relativeFlat f M hM hU` gives flatness of the
original `Γ(M,U)` over the base ring. Its literal scalar map is
`(ΓSpecIso A).inv ≫ f.appLE ⊤ U`; `SpecMap_affineOpen_baseRingHom` identifies
its spectrum map with the original affine chart followed by `f`. The section
comparison is the original affine-open restriction-unit linear equivalence.
These section results require quasicoherence, relative flatness and
affineness of the chosen open. They require neither Noetherianity,
separatedness of `X` nor flatness of the scheme morphism. No generic affine
tensor/section isomorphism or additional theorem-family premise is introduced.

The AffineSections leaf passed alone with receipt `1792092914329725000-53974`.
Its current consumer is flatness of the original affine-intersection terms
of the structural-ring Cech complex.
The external `work/proper-validation/RelativeFlatConsumer.lean` was refreshed
to check actual affine-spectrum sections, arbitrary affine-open sections and
the literal base-ring stalk action. It passed with receipt
`1792092982505594000-55363`; the inspected locality and section proofs use only
`propext`, `Classical.choice` and `Quot.sound`.

`relativeFlat_of_comp_isOpenImmersion` transports relative flatness from
`b ≫ j` to `b` when `j` is an actual open immersion, through the native
isomorphism of the two base stalk rings. The scalar-restriction equivalence
retains the actual stalk maps. `relativeFlat_pullback_of_isOpenImmersion`
then proves relative flatness of the ordinary coefficient pullback on the
actual fibre product over an open target. Both helpers require no
quasicoherence, Noetherianity or flatness of the original morphism. The
[general-target proper Grauert descent](../../../Cohomology/DirectImage/Proper/Grauert.lean)
uses this target-open transport.

`Aglib.AlgebraicGeometry.Modules.Flat.Relative.OfSections` proves the converse
of `flat_affineOpen_sections_of_relativeFlat`. For `f : X ⟶ Spec A` and a
quasicoherent `M`, `relativeFlat_of_flat_affineOpen_sections` derives
`relativeFlat f M` from flat sections on an affine open neighbourhood of every
point, and `relativeFlat_iff_flat_affineOpen_sections` says that relative
flatness over an affine base is flatness of all affine sections (Stacks
Project, Tag 01U4). `relativeFlat_specMap_of_flat` is the case of
`Spec B ⟶ Spec A`. This is the last step of Nitsure's Lemma 3.2.

`Aglib.AlgebraicGeometry.Modules.Flat.Relative.Tensor` proves
`relativeFlat_tensor_of_locallyTrivial`: tensoring with a sheaf that is
locally isomorphic to the structure module preserves relative flatness. No
quasicoherence is assumed.

`Aglib.AlgebraicGeometry.Modules.Flat.Relative.Coproduct` proves
`relativeFlat_coproduct`: a coproduct of relatively flat modules, over any
index type, is relatively flat.

Import `Aglib.AlgebraicGeometry.Modules.Flat.Relative.BaseChange` for base
change of relative flatness, the global ("in particular") statement of Stacks
Project, Tag 01U8; the pointwise form is not formalized. For a pullback
square `h : IsPullback g q p f` and a quasicoherent `M` with
`relativeFlat p M`, `relativeFlat_pullback_of_isPullback h M hM` proves
`relativeFlat q ((pullback g).obj M)`; `relativeFlat_pullback_snd` is the
canonical-pullback form, which for `f = Spec.map σ` is the affine base change
along `σ : A ⟶ A'`. The proof restricts the square to affine opens with
Mathlib's `Scheme.Hom.isPullback_resLE` and uses only `appTop` maps: the ring
pushout `isPushout_appTop_of_isPullback`, the section comparison
`affinePullbackSectionsIso`, the open-restriction square `pullbackOpenSquare`
and the algebraic core `ModuleCat.flat_extendScalars_of_isPushout` of
[ChangeOfRings/BaseChange](../../../../Algebra/Category/ModuleCat/ChangeOfRings/BaseChange.lean)
(Stacks Project, Tag 00HI). Between affine schemes,
`relativeFlat_iff_flat_affineΓFunctor` identifies relative flatness of a
quasicoherent module with flatness of its `affineΓFunctor` sections over the
target sections through `appTop`; with `flat_affineOpen_sections_of_relativeFlat`
it is the affine case of Stacks, Tag 01U4. `relativeFlat_comp_of_isOpenImmersion`
is the converse of `relativeFlat_of_comp_isOpenImmersion`. Quasicoherence is
assumed, as in the Stacks statement; no finiteness, Noetherianity or flatness
of a morphism is assumed.

`Aglib.AlgebraicGeometry.Modules.Flat.Relative.LocalOnBase` (`LocalOnBase.lean`): for a pullback
square of `p` along `g` and quasicoherent `M`, flatness of the pulled-back module restricts along
any `j : U ⟶ T` (`relativeFlat_of_isPullback_comp`) and is local on `T` for open-immersion covers
(`relativeFlat_of_isPullback_of_forall_exists`). It is a sibling leaf of `Locality`, which keeps
its open-restriction statements.

`Aglib.AlgebraicGeometry.Modules.Flat.Relative.PullbackSquare` (`PullbackSquare.lean`): for a
pullback square `IsPullback a b p j`, quasi-coherent `M` and `g' : T ⟶ Y`, the base change of `M`
along `g' ≫ j` is flat over `T` iff the base change of `a^* M` along `g'` is
(`relativeFlat_pullback_comp_iff_of_isPullback`); for two pullback squares of `p` along the same
`g`, the pulled-back modules are flat together (`relativeFlat_iff_of_isPullback`); and, for the
chosen pullbacks, restriction to opens of `T` and locality on `T`
(`relativeFlat_pullback_snd_opensι`, `relativeFlat_pullback_snd_of_forall_opens`, restating
`LocalOnBase`). The flattening stratification over a locally Noetherian base consumes it. It is a
sibling leaf of `LocalOnBase`.

`Aglib.AlgebraicGeometry.Modules.Flat.Relative.Unit` treats the structure
module. Its actual stalks are free of rank one (`unitStalkIso`, through
`unitStalkCorepresentable`) and flat over the local rings (`unit_stalk_flat`,
an instance). For a flat morphism `f`, `relativeFlat_unit_of_flat f` proves
relative flatness of the structure module over the target, by transitivity of
flatness along `f.stalkMap x`. No Noetherianity, quasicompactness or properness
is assumed. The consumers are the proper local criterion for the structure
sheaf and `ProjectiveSpace/Tensor/Flat`.

Import `Aglib.AlgebraicGeometry.Modules.Flat.Relative.ClosedSubscheme` for closed subschemes:
`relativeFlat_quotientModule_iff_flat` (the structure module `𝒪_X / I_W` is relatively flat over
`S` exactly when `W ⟶ X ⟶ S` is flat, through the stalks of `i_* 𝒪_W`,
`pushforwardUnitStalkIso`), `relativeFlat_pullback_quotientModule_iff` (the same for `f^* 𝒪_W`,
with no flatness of `W`) and `relativeFlat_idealModule_of_flat` (the ideal module of a flat closed
subscheme over a flat affine base).

[LocalOnTarget](LocalOnTarget.lean) proves that relative flatness of a module `M` on `X` over `T`
is local on `T` through arbitrary cartesian squares over open immersions
(`relativeFlat_of_forall_isPullback`), with the point-lifting step
`exists_apply_eq_of_isPullback`; the counterpart of `relativeFlat_of_isPullback_of_forall_exists`
([LocalOnBase](LocalOnBase.lean)) for modules not pulled back from a base.
