/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap

/-! # Composition of the original Ext diagram transformations

The complete diagram equation uses the actual exact-functor comparison and
source coherence, with the original index functors and target whiskering.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Functor

universe i₀ j₀ i₁ j₁ i₂ j₂ u₀ v₀ u₁ v₁ u₂ v₂ w

variable {C₀ : Type u₀} [Category.{v₀} C₀] [Abelian C₀] [HasExt.{w} C₀]
  {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasExt.{w} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasExt.{w} C₂]
  {I₀ : Type i₀} [Category.{j₀} I₀] {I₁ : Type i₁} [Category.{j₁} I₁]
  {I₂ : Type i₂} [Category.{j₂} I₂]

/-- The whole original transfer diagram composes from its actual source
coherence. Its common Ext universe is the natural-transformation codomain. -/
theorem extDiagramMap_comp
    (L₁ : C₀ ⥤ C₁) [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    (L₂ : C₁ ⥤ C₂) [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    (L₀ : C₀ ⥤ C₂) [L₀.Additive] [PreservesFiniteLimits L₀] [PreservesFiniteColimits L₀]
    (c : L₀ ≅ L₁ ⋙ L₂)
    (F : I₀ ⥤ C₀) (G : I₁ ⥤ C₁) (K : I₂ ⥤ C₂)
    (H₁ : I₀ ⥤ I₁) (H₂ : I₁ ⥤ I₂)
    (e₁ : F ⋙ L₁ ≅ H₁ ⋙ G) (e₂ : G ⋙ L₂ ≅ H₂ ⋙ K)
    (e₀ : F ⋙ L₀ ≅ (H₁ ⋙ H₂) ⋙ K)
    (hs : ∀ U, e₀.inv.app U ≫ c.hom.app (F.obj U) =
      e₂.inv.app (H₁.obj U) ≫ L₂.map (e₁.inv.app U))
    {A : C₀} {B : C₁} {C : C₂} (a : L₁.obj A ⟶ B) (b : L₂.obj B ⟶ C) (n : ℕ) :
    L₁.extDiagramMap F (H₁ ⋙ G) e₁ a n ≫
        whiskerLeft H₁.op (L₂.extDiagramMap G (H₂ ⋙ K) e₂ b n) =
      L₀.extDiagramMap F ((H₁ ⋙ H₂) ⋙ K) e₀
        (c.hom.app A ≫ L₂.map a ≫ b) n := by
  ext U x
  exact DFunLike.congr_fun (extCoefficientTransfer_comp L₁ L₂ L₀ c
    (e₁.inv.app U.unop) (e₂.inv.app (H₁.obj U.unop)) (e₀.inv.app U.unop)
    (hs U.unop) a b n) x

end CategoryTheory.Functor
