/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Unit
public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Sections

/-!
# Right-unit compatibility of the canonical pullback tensor map

For a morphism of schemes `f : X ⟶ Y` and a module `M` on `Y`, the canonical comparison
`pullbackTensorMap f M 𝒪_Y : f^*(M ⊗ 𝒪_Y) ⟶ f^*M ⊗ f^*𝒪_Y`, followed by
`pullbackUnitIso f : f^*𝒪_Y ≅ 𝒪_X` on the second factor, carries the pulled-back inverse right
unitor of `M` to the inverse right unitor of `f^*M` (`pullbackTensorMap_rightUnit`). This is the
right-hand companion of `pullbackTensorMap_leftUnit`.

The proof passes to the adjoint maps `M ⟶ f_*(f^*M ⊗ 𝒪_X)` and compares them on sections: both
send `m` to the pure tensor `η(m) ⊗ 1`, where `η` is the unit of the pullback-pushforward
adjunction, since `pullbackUnitIso f` sends `η(1)` to `1` (`pullbackUnitIso_hom_unit_one`).
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

-- Sections of the unit module are written as ring sections `Γ(Y, U)`.
set_option backward.isDefEq.respectTransparency false in
/-- The pullback-unit comparison sends the adjunction-unit image of `1` to `1`. -/
theorem pullbackUnitIso_hom_unit_one (U : Y.Opens) :
    (pullbackUnitIso f).hom.val.app (op (f ⁻¹ᵁ U))
      (((pullbackPushforwardAdjunction f).unit.app (SheafOfModules.unit Y.ringCatSheaf)).val.app
        (op U) (1 : Γ(Y, U))) = (1 : Γ(X, f ⁻¹ᵁ U)) := by
  have h := pullbackUnitIso_homEquiv f
  rw [Adjunction.homEquiv_unit] at h
  change ((((pullbackPushforwardAdjunction f).unit.app (SheafOfModules.unit Y.ringCatSheaf)) ≫
    (pushforward f).map (pullbackUnitIso f).hom).val.app (op U)) (1 : Γ(Y, U)) = _
  rw [h]
  exact map_one (f.app U).hom

-- The pure tensors of the sheafified tensor are written with the sheafification unit on one side
-- and `moduleTensorSection` on the other; their scalar rings differ only in presentation.
set_option backward.isDefEq.respectTransparency false in
/-- **Right-unit compatibility of the pullback tensor comparison**:
`f^*(ρ_M)⁻¹ ≫ pullbackTensorMap f M 𝒪_Y ≫ (f^*M ◁ pullbackUnitIso f) = (ρ_{f^*M})⁻¹`. -/
theorem pullbackTensorMap_rightUnit (M : Y.Modules) :
    (pullback f).map (ρ_ M).inv ≫ pullbackTensorMap f M (𝟙_ Y.Modules) ≫
        ((pullback f).obj M ◁ (pullbackUnitIso f).hom) =
      (ρ_ ((pullback f).obj M)).inv := by
  apply ((pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  erw [pullbackTensorMap_adjoint]
  rw [Adjunction.homEquiv_unit]
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  let uM := (pullbackPushforwardAdjunction f).unit.app M
  let u1 := (pullbackPushforwardAdjunction f).unit.app (𝟙_ Y.Modules)
  have h1 : (ρ_ M).inv.val.app (op U) m =
      (tensorSheafUnit Y M (𝟙_ Y.Modules)).app (op U) (m ⊗ₜ (1 : Γ(Y, U))) :=
    rightUnitor_inv_moduleTensorSection M U m
  have h6 : (ρ_ ((pullback f).obj M)).inv.val.app (op (f ⁻¹ᵁ U)) (uM.val.app (op U) m) =
      (tensorSheafUnit X ((pullback f).obj M) (𝟙_ X.Modules)).app (op (f ⁻¹ᵁ U))
        (uM.val.app (op U) m ⊗ₜ (1 : Γ(X, f ⁻¹ᵁ U))) :=
    rightUnitor_inv_moduleTensorSection _ (f ⁻¹ᵁ U) _
  have h4 := whiskerLeft_moduleTensorSection ((pullback f).obj M) (pullbackUnitIso f).hom
    (f ⁻¹ᵁ U) (uM.val.app (op U) m) (u1.val.app (op U) (1 : Γ(Y, U)))
  change ((pullback f).obj M ◁ (pullbackUnitIso f).hom).val.app (op (f ⁻¹ᵁ U))
      ((pushforwardTensorMap f ((pullback f).obj M) ((pullback f).obj (𝟙_ Y.Modules))).val.app
        (op U) ((tensorSheafMap Y uM u1).val.app (op U) ((ρ_ M).inv.val.app (op U) m))) =
    (ρ_ ((pullback f).obj M)).inv.val.app (op (f ⁻¹ᵁ U)) (uM.val.app (op U) m)
  have h2 := tensorSheafMap_tmul Y uM u1 (op U) m (1 : Γ(Y, U))
  have h3 := pushforwardTensorMap_tmul f ((pullback f).obj M) ((pullback f).obj (𝟙_ Y.Modules))
    (op U) (uM.val.app (op U) m) (u1.val.app (op U) (1 : Γ(Y, U)))
  rw [h1]
  erw [h2, h3, h6]
  refine h4.trans ?_
  erw [pullbackUnitIso_hom_unit_one f U]
  rfl

end AlgebraicGeometry.Scheme.Modules
