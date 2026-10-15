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
