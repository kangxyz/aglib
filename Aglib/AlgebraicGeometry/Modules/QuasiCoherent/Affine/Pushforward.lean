/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
/-!
# Actual pushforward along a map of affine schemes

Global sections of the genuine sheaf pushforward are restriction of scalars.
The comparison uses mathlib's pushforward of module sheaves, including its
structure-sheaf action. Quasicoherence is proved from the localization
criterion, independently of finite generation or closedness.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- Global sections of the actual affine pushforward are restriction of
scalars along the original coordinate-ring homomorphism. -/
def pushforwardGlobalSectionsIso :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom := by
  exact Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso φ)
    (TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op ⊤))

/-- Pushforward along any affine spectrum map preserves quasicoherence. -/
theorem isQuasicoherent_pushforward (M : (Spec S).Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward (Spec.map φ)).obj M).IsQuasicoherent := by
  rw [isQuasicoherent_iff_isIso_fromTildeΓ]
  exact isIso_fromTildeΓ_pushforward φ M

/-- Sheafifying after restriction of scalars agrees naturally with the actual
pushforward of the associated sheaf. The counit in this comparison is the
actual `fromTildeΓ` map of the pushforward sheaf. -/
def tildePushforwardIso :
    tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ) ≅
      ModuleCat.restrictScalars φ.hom ⋙ tilde.functor R := by
  let F := tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ)
  have h (M : ModuleCat S) : (F.obj M).IsQuasicoherent :=
    isQuasicoherent_pushforward φ (tilde M)
  let e : (F ⋙ moduleSpecΓFunctor) ⋙ tilde.functor R ≅ F :=
    NatIso.ofComponents (fun M ↦ asIso (F.obj M).fromTildeΓ)
      (fun f ↦ Scheme.Modules.fromTildeΓNatTrans.naturality (F.map f))
  let d : F ⋙ moduleSpecΓFunctor ≅ ModuleCat.restrictScalars φ.hom :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (tilde.functor S) (pushforwardGlobalSectionsIso φ) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (tilde.toTildeΓNatIso (R := S)).symm _ ≪≫
      Functor.leftUnitor _
  exact e.symm ≪≫ Functor.isoWhiskerRight d (tilde.functor R)

end AlgebraicGeometry.Scheme.Modules
