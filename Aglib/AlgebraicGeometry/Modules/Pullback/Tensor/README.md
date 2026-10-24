# Pullback and tensor products of arbitrary module sheaves

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Basic`, owns `Scheme.Modules.pullbackTensorMap`, its actual adjoint equation and both-variable naturality. For arbitrary `f : X → Y` and `M N : Y.Modules`, its adjoint is the tensor of the pullback-adjunction units followed by the canonical `pushforwardTensorMap`. The direct-image arrow specializes the existing continuous ringed-site tensor map; no cocontinuity or invertibility hypothesis is added.

[Unit](Unit.lean) proves the unit law, unit-case invertibility and transport along a supplied global unit trivialization. It uses the existing native pullback-unit isomorphism. [Restriction](Restriction.lean) uses the existing `tensorRestrictionIso` and retains the literal mate-defined `Pullback.OpenRestriction.localPullbackIso` in the pullback-tensor square. The ordinary restricted-unit and direct-image section identities belong to [OpenRestriction](../OpenRestriction.lean).

[RightUnit](RightUnit.lean) proves the right-unit law `pullbackTensorMap_rightUnit`: `f^*(ρ_M)⁻¹ ≫ pullbackTensorMap f M 𝒪_Y ≫ (f^*M ◁ pullbackUnitIso f) = (ρ_{f^*M})⁻¹`, comparing adjoint maps on pure section tensors through `pullbackUnitIso_hom_unit_one`. It is stated with the monoidal `ρ_` and `◁`, while the left law of [Unit](Unit.lean) uses `tensorSheafMap` and `tensorSheafLeftUnit`.

[Isomorphism](Isomorphism.lean), imported as `Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Isomorphism`, constructs an inverse to this same canonical comparison for arbitrary scheme morphisms and arbitrary module sheaves. No rank, quasicoherence, flatness or finiteness hypothesis is added. Its namespace is `Scheme.Modules.Pullback.Tensor`: `tensorHomEquiv` and `pushforwardHomIso` use the actual internal Hom and restricted pullback adjunction; `pullbackTensorInverse`, `pullbackTensorMap_inverse` and `pullbackTensorInverse_map` fix both inverse equations.

The tensor objects, maps and sheafification unit are the common scheme specializations in [Tensor/Basic](../../Tensor/Basic.lean). [InternalHom](../../InternalHom.lean) and ordinary restriction precede this family. Rank-one, line-bundle and additive Picard pullback consequences remain in [Invertible/PullbackTensor/Local](../../Invertible/PullbackTensor/Local.lean). No old generic invertible-name aliases or second tensor comparison are introduced.

[Pairing](Pairing.lean) pulls back a pairing `ε : N ⊗ L ⟶ 𝒪_P` along `p` (`pullbackPairing`,
`pullbackPairingOf`) and proves its composition and base-change laws
(`pullback_map_pullbackPairing`, `pullbackPairingOf_pullback`), with no flatness, finiteness or
quasicoherence hypothesis; `tensorSheafIso_hom` and `tensorSheafIso_inv` are the `rfl` formulas
for `tensorSheafIso` of [Tensor/Basic](../../Tensor/Basic.lean). Its `pullbackTensorMapIso f M N`
is `asIso (pullbackTensorMap f M N)`, the pointwise form of
`Invertible.pullbackTensorIso moduleTensorPullback f M N`
([Invertible/PullbackTensor/Properties](../../Invertible/PullbackTensor/Properties.lean)) without
that declaration's legacy `ModuleTensorPullback` premise.

[PairingComp](PairingComp.lean): `pullbackPairing p ((a ⊗ 𝟙) ≫ ε) = (p^* a ⊗ 𝟙) ≫ pullbackPairing p ε`
(`pullbackPairing_tensorSheafMap_comp`), for every morphism `p` and all modules.

[PairingEquiv](PairingEquiv.lean): tensoring with a line bundle is fully faithful
(`Invertible.tensorRightFullyFaithful`); for a perfect pairing `ε : N ⊗ L ≅ 𝒪` with `L` a line
bundle, `j ↦ pullbackPairingOf p ε j` is a bijection `Hom(M, p^* N) ≃ Hom(M ⊗ p^* L, 𝒪)`
(`pullbackPairingOfEquiv`).
