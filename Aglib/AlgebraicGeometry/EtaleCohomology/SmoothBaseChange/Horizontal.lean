/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Cartesian

/-! # Horizontal composition and cancellation of original higher exchange

The native exact pasting equation proves composition and cancellation. At an
actual étale cartesian second square, the accepted original comparison supplies
the invertible second exchange. Its four required derived-category universes
stay independent; the two ordinary pasting arguments require no derived models.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u v dX₀ dX₁ dX₂ dS₀ dS₁ dS₂

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

section Horizontal

variable {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}}
  [HasDerivedCategory.{dX₀} (AbelianSheaf.{u, u + 1} X₀)]
  [HasDerivedCategory.{dX₁} (AbelianSheaf.{u, u + 1} X₁)]
  [HasDerivedCategory.{dX₂} (AbelianSheaf.{u, u + 1} X₂)]
  [HasDerivedCategory.{dS₀} (AbelianSheaf.{u, u + 1} S₀)]
  [HasDerivedCategory.{dS₁} (AbelianSheaf.{u, u + 1} S₁)]
  [HasDerivedCategory.{dS₂} (AbelianSheaf.{u, u + 1} S₂)]
  (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
  (g₁ : S₁ ⟶ S₀) (g₂ : S₂ ⟶ S₁) (h₁ : X₁ ⟶ X₀) (h₂ : X₂ ⟶ X₁)
  (e₁ : f₁ ≫ g₁ = h₁ ≫ f₀) (e₂ : f₂ ≫ g₂ = h₂ ≫ f₁)
  (e : f₂ ≫ (g₂ ≫ g₁) = (h₂ ≫ h₁) ≫ f₀)
  (F : AbelianSheaf.{u, u + 1} X₀) (q : ℕ)

omit [HasDerivedCategory.{dX₀} (AbelianSheaf.{u, u + 1} X₀)]
  [HasDerivedCategory.{dX₁} (AbelianSheaf.{u, u + 1} X₁)]
  [HasDerivedCategory.{dX₂} (AbelianSheaf.{u, u + 1} X₂)]
  [HasDerivedCategory.{dS₀} (AbelianSheaf.{u, u + 1} S₀)]
  [HasDerivedCategory.{dS₁} (AbelianSheaf.{u, u + 1} S₁)]
  [HasDerivedCategory.{dS₂} (AbelianSheaf.{u, u + 1} S₂)] in
/-- Original higher exchange is stable under horizontal composition at the
specified coefficient, with the literal pulled-back coefficient on the second square. -/
theorem higherBaseChangeMap_isIso_hComp
    [IsIso ((higherBaseChangeMap f₀ f₁ g₁ h₁ e₁ q).app F)]
    [IsIso ((higherBaseChangeMap f₁ f₂ g₂ h₂ e₂ q).app ((inverseImage h₁).obj F))] :
    IsIso ((higherBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e q).app F) := by
  have hp := higherBaseChangeMap_hComp f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e q F
  dsimp only [MappedHorizontalPastingEquation] at hp
  apply (isIso_comp_right_iff _
    ((higherDirectImage f₂ q).map ((inverseImageComp h₁ h₂).hom.app F))).mp
  rw [← hp]
  infer_instance

omit [HasDerivedCategory.{dX₀} (AbelianSheaf.{u, u + 1} X₀)]
  [HasDerivedCategory.{dX₁} (AbelianSheaf.{u, u + 1} X₁)]
  [HasDerivedCategory.{dX₂} (AbelianSheaf.{u, u + 1} X₂)]
  [HasDerivedCategory.{dS₀} (AbelianSheaf.{u, u + 1} S₀)]
  [HasDerivedCategory.{dS₁} (AbelianSheaf.{u, u + 1} S₁)]
  [HasDerivedCategory.{dS₂} (AbelianSheaf.{u, u + 1} S₂)] in
/-- Cancelling the original second exchange detects the first exchange after
its actual inverse image; neither a replacement endpoint isomorphism nor a
conservativity assumption is hidden here. -/
theorem higherBaseChangeMap_inverseImage_isIso_of_hComp
    [IsIso ((higherBaseChangeMap f₁ f₂ g₂ h₂ e₂ q).app ((inverseImage h₁).obj F))]
    [IsIso ((higherBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e q).app F)] :
    IsIso ((inverseImage g₂).map ((higherBaseChangeMap f₀ f₁ g₁ h₁ e₁ q).app F)) := by
  have hp := higherBaseChangeMap_hComp f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e q F
  dsimp only [MappedHorizontalPastingEquation] at hp
  have hi : IsIso
      ((inverseImageComp g₁ g₂).hom.app ((higherDirectImage f₀ q).obj F) ≫
        (inverseImage g₂).map ((higherBaseChangeMap f₀ f₁ g₁ h₁ e₁ q).app F) ≫
        (higherBaseChangeMap f₁ f₂ g₂ h₂ e₂ q).app ((inverseImage h₁).obj F)) := by
    rw [hp]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp ((isIso_comp_left_iff _ _).mp hi)

omit [HasDerivedCategory.{dX₀} (AbelianSheaf.{u, u + 1} X₀)]
  [HasDerivedCategory.{dS₀} (AbelianSheaf.{u, u + 1} S₀)] in
/-- At a single actual étale cartesian restriction, original composite exchange
invertibility detects the inverse image of the first exchange. The original
natural-isomorphism component is typed before an indexed chart is substituted. -/
theorem higherBaseChangeMap_inverseImage_isIso_of_etale_hComp
    [Etale g₂] (hp : IsPullback h₂ f₂ f₁ g₂)
    (hcomp : IsIso ((higherBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e q).app F)) :
    IsIso ((inverseImage g₂).map ((higherBaseChangeMap f₀ f₁ g₁ h₁ e₁ q).app F)) := by
  let : IsIso (higherBaseChangeMap f₁ f₂ g₂ h₂ hp.w.symm q) :=
    higherBaseChangeMap_etale_isIso_of_isPullback f₁ f₂ g₂ h₂ hp q
  let : IsIso ((higherBaseChangeMap f₁ f₂ g₂ h₂ hp.w.symm q).app
      ((inverseImage h₁).obj F)) :=
    NatIso.isIso_app_of_isIso _ _
  let : IsIso ((higherBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e q).app F) := hcomp
  exact higherBaseChangeMap_inverseImage_isIso_of_hComp f₀ f₁ f₂ g₁ g₂ h₁ h₂
    e₁ hp.w.symm e F q

end Horizontal

end AlgebraicGeometry.Scheme.EtaleCohomology
