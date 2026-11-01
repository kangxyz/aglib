/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.External

/-! Original structure modules and original coefficient maps remain the
unit and map data of the external tensor on the actual fibre product. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

example :
    ((externalTensor f g).obj (SheafOfModules.unit X.ringCatSheaf)).obj
        (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit (Limits.pullback f g : Scheme).ringCatSheaf :=
  (externalTensorLeftUnitIso f g).app (SheafOfModules.unit Y.ringCatSheaf) ≪≫
    pullbackUnitIso (Limits.pullback.snd f g)

example (z : (Limits.pullback f g : Scheme)) (M : X.Modules)
    {N N' : Y.Modules} (b : N ⟶ N') :
    (moduleStalk (Limits.pullback f g) z).map (((externalTensor f g).obj M).map b) ≫
        (externalTensorStalkIso f g z M N').hom =
      (externalTensorStalkIso f g z M N).hom ≫
        (𝟙 ((ModuleCat.extendScalars ((Limits.pullback.fst f g).stalkMap z).hom).obj
            ((moduleStalk X (Limits.pullback.fst f g z)).obj M)) ⊗ₘ
          (ModuleCat.extendScalars ((Limits.pullback.snd f g).stalkMap z).hom).map
            ((moduleStalk Y (Limits.pullback.snd f g z)).map b)) :=
  externalTensorStalkIso_naturality_right f g z M b

section Field

variable {k : Type u} [Field k] (π : X ⟶ Spec (.of k)) (ρ : Y ⟶ Spec (.of k))

example (M : X.Modules) : PreservesFiniteLimits ((externalTensor π ρ).obj M) :=
  inferInstance

example (M : X.Modules) : PreservesFiniteColimits ((externalTensor π ρ).obj M) :=
  inferInstance

example (N : Y.Modules) : PreservesFiniteLimits ((externalTensor π ρ).flip.obj N) :=
  inferInstance

example (N : Y.Modules) : PreservesFiniteColimits ((externalTensor π ρ).flip.obj N) :=
  inferInstance

end Field
