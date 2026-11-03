/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.DiagramTransfer
public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.Composition

/-! # Composition on the literal native cohomology presheaves

The whole composition law shares the same original constructor as its geometric
instances, with the actual inverse-image comparison and source coherence.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Sheaf

universe u₀ v₀ u₁ v₁ u₂ v₂ w

variable {C₀ : Type u₀} [Category.{v₀} C₀]
  {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁)
  (J₂ : GrothendieckTopology C₂)
  [HasSheafify J₀ AddCommGrpCat.{v₀}] [HasSheafify J₁ AddCommGrpCat.{v₁}]
  [HasSheafify J₂ AddCommGrpCat.{v₂}]
  [HasExt.{w} (Sheaf J₀ AddCommGrpCat.{v₀})]
  [HasExt.{w} (Sheaf J₁ AddCommGrpCat.{v₁})]
  [HasExt.{w} (Sheaf J₂ AddCommGrpCat.{v₂})]

local notation "F₀" =>
  (yoneda ⋙ Functor.obj (Functor.whiskeringRight C₀ᵒᵖ _ _) AddCommGrpCat.free ⋙
    presheafToSheaf J₀ AddCommGrpCat)
local notation "F₁" =>
  (yoneda ⋙ Functor.obj (Functor.whiskeringRight C₁ᵒᵖ _ _) AddCommGrpCat.free ⋙
    presheafToSheaf J₁ AddCommGrpCat)
local notation "F₂" =>
  (yoneda ⋙ Functor.obj (Functor.whiskeringRight C₂ᵒᵖ _ _) AddCommGrpCat.free ⋙
    presheafToSheaf J₂ AddCommGrpCat)

/-- The original native presheaf transfers compose with their actual source
coherence and canonical exact-functor comparison. -/
theorem cohomologyPresheafTransfer_comp
    (L₁ : Sheaf J₀ AddCommGrpCat.{v₀} ⥤ Sheaf J₁ AddCommGrpCat.{v₁})
    [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    (L₂ : Sheaf J₁ AddCommGrpCat.{v₁} ⥤ Sheaf J₂ AddCommGrpCat.{v₂})
    [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    (L₀ : Sheaf J₀ AddCommGrpCat.{v₀} ⥤ Sheaf J₂ AddCommGrpCat.{v₂})
    [L₀.Additive] [PreservesFiniteLimits L₀] [PreservesFiniteColimits L₀]
    (c : L₀ ≅ L₁ ⋙ L₂) (H₁ : C₀ ⥤ C₁) (H₂ : C₁ ⥤ C₂)
    (e₁ : F₀ ⋙ L₁ ≅ H₁ ⋙ F₁) (e₂ : F₁ ⋙ L₂ ≅ H₂ ⋙ F₂)
    (e₀ : F₀ ⋙ L₀ ≅ (H₁ ⋙ H₂) ⋙ F₂)
    (hs : ∀ U, e₀.inv.app U ≫ c.hom.app (Functor.obj F₀ U) =
      e₂.inv.app (H₁.obj U) ≫ L₂.map (e₁.inv.app U))
    {A : Sheaf J₀ AddCommGrpCat.{v₀}} {B : Sheaf J₁ AddCommGrpCat.{v₁}}
    {C : Sheaf J₂ AddCommGrpCat.{v₂}}
    (a : L₁.obj A ⟶ B) (b : L₂.obj B ⟶ C) (n : ℕ) :
    cohomologyPresheafTransfer J₀ J₁ L₁ H₁ e₁ a n ≫
        Functor.whiskerLeft H₁.op (cohomologyPresheafTransfer J₁ J₂ L₂ H₂ e₂ b n) =
      cohomologyPresheafTransfer J₀ J₂ L₀ (H₁ ⋙ H₂) e₀
        (c.hom.app A ≫ L₂.map a ≫ b) n :=
  L₁.extDiagramMap_comp L₂ L₀ c F₀ F₁ F₂ H₁ H₂ e₁ e₂ e₀ hs a b n

end CategoryTheory.Sheaf
