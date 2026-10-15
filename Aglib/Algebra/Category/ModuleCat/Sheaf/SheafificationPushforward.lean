/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
/-!
# Sheafification and continuous cocontinuous pushforward

The original sheafification unit and counit define the comparison. Cocontinuity preserves
local bijectivity, giving its invertibility. The literal unit compatibility is retained.
-/


/-!
Source: `Quillen/Algebra/Category/ModuleCat/Sheaf/SheafificationPushforward.lean` at LOCAL
Quillen `189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Selection: whole_general_prerequisite; source ranges [[1, 99]].
Actual objects, maps, universes and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace SheafOfModules
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    [F.IsContinuous J K]
    [HasWeakSheafify J AddCommGrpCat.{v}] [HasWeakSheafify K AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{v}]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
/-- The original identity on the source ring presheaf is locally injective. -/
local instance sourceIdentityLocallyInjective : Presheaf.IsLocallyInjective K (𝟙 R.obj) :=
  Presheaf.isLocallyInjective_of_injective K _ (fun _ => Function.injective_id)
/-- The original identity on the source ring presheaf is locally surjective. -/
local instance sourceIdentityLocallySurjective : Presheaf.IsLocallySurjective K (𝟙 R.obj) :=
  Presheaf.isLocallySurjective_of_surjective K _ (fun _ => Function.surjective_id)
/-- The canonical comparison obtained from the original source unit and target counit. -/
def sheafificationPushforwardComparison :
    PresheafOfModules.pushforward.{v} φ.hom ⋙
        PresheafOfModules.sheafification.{v} (R := S) (𝟙 S.obj) ⟶
      PresheafOfModules.sheafification.{v} (R := R) (𝟙 R.obj) ⋙ pushforward.{v} φ :=
  whiskerRight (whiskerRight
    (PresheafOfModules.sheafificationAdjunction.{v} (R := R) (𝟙 R.obj)).unit
      (PresheafOfModules.pushforward φ.hom))
    (PresheafOfModules.sheafification.{v} (R := S) (𝟙 S.obj)) ≫
      whiskerLeft (PresheafOfModules.sheafification.{v} (R := R) (𝟙 R.obj) ⋙ pushforward.{v} φ)
        (PresheafOfModules.sheafificationAdjunction.{v} (R := S) (𝟙 S.obj)).counit
/-- Its component is the original sheafified restricted unit followed by the original counit. -/
theorem sheafificationPushforwardComparison_app (M : PresheafOfModules.{v} R.obj) :
    (sheafificationPushforwardComparison φ).app M =
      (PresheafOfModules.sheafification.{v} (R := S) (𝟙 S.obj)).map
        ((PresheafOfModules.pushforward φ.hom).map
          ((PresheafOfModules.sheafificationAdjunction.{v} (R := R) (𝟙 R.obj)).unit.app M)) ≫
      (PresheafOfModules.sheafificationAdjunction.{v} (R := S) (𝟙 S.obj)).counit.app
        ((pushforward.{v} φ).obj ((PresheafOfModules.sheafification.{v} (R := R) (𝟙 R.obj)).obj
    M)) :=
  rfl
/-- The comparison preserves the literal original sheafification unit. -/
theorem sheafificationPushforwardComparison_unit (M : PresheafOfModules.{v} R.obj) :
    (PresheafOfModules.sheafificationAdjunction.{v} (R := S) (𝟙 S.obj)).unit.app
        ((PresheafOfModules.pushforward φ.hom).obj M) ≫
      (forget S).map ((sheafificationPushforwardComparison φ).app M) =
    (PresheafOfModules.pushforward φ.hom).map
      ((PresheafOfModules.sheafificationAdjunction.{v} (R := R) (𝟙 R.obj)).unit.app M) := by
  apply (PresheafOfModules.sheafificationAdjunction.{v}
    (R := S) (𝟙 S.obj)).unit_comp_map_eq_iff _ _ |>.mpr
  exact sheafificationPushforwardComparison_app φ M
/-- Cocontinuity makes the original sheafified restricted unit invertible. -/
theorem isIso_sheafification_pushforward_unit [F.IsCocontinuous J K]
    (M : PresheafOfModules.{v} R.obj) :
    IsIso ((PresheafOfModules.sheafification.{v} (R := S) (𝟙 S.obj)).map
      ((PresheafOfModules.pushforward φ.hom).map
        ((PresheafOfModules.sheafificationAdjunction.{v} (R := R) (𝟙 R.obj)).unit.app M))) := by
  rw [← isIso_iff_of_reflects_iso _ (toSheaf S)]
  change IsIso ((presheafToSheaf J AddCommGrpCat.{v}).map
    (whiskerLeft F.op (CategoryTheory.toSheafify K M.presheaf)))
  let : Presheaf.IsLocallyInjective J
      (whiskerLeft F.op (CategoryTheory.toSheafify K M.presheaf)) :=
    Presheaf.isLocallyInjective_whisker J K F _
  let : Presheaf.IsLocallySurjective J
      (whiskerLeft F.op (CategoryTheory.toSheafify K M.presheaf)) :=
    Presheaf.isLocallySurjective_whisker J K F _
  exact (J.W_iff _).mp (J.W_of_isLocallyBijective _)
/-- With cocontinuity, the original comparison is an isomorphism. -/
instance sheafificationPushforwardComparison_isIso [F.IsCocontinuous J K] :
    IsIso (sheafificationPushforwardComparison φ) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [sheafificationPushforwardComparison_app]
  have := isIso_sheafification_pushforward_unit φ M
  infer_instance
/-- The original sheafification comparison for a continuous, cocontinuous site functor. -/
def sheafificationPushforwardIso [F.IsCocontinuous J K] :
    PresheafOfModules.pushforward.{v} φ.hom ⋙
        PresheafOfModules.sheafification.{v} (R := S) (𝟙 S.obj) ≅
      PresheafOfModules.sheafification.{v} (R := R) (𝟙 R.obj) ⋙ pushforward.{v} φ :=
  asIso (sheafificationPushforwardComparison φ)
end SheafOfModules
