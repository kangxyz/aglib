/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.Composition
public import Mathlib.CategoryTheory.Square

/-! # Complete composition data of the original Ext diagram transformations

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

/-- The original composition triangle as a complete square with an identity
bottom edge. All three transfer maps and their law are built before specialization. -/
def extDiagramCompositionSquare
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
    Square (I₀ᵒᵖ ⥤ AddCommGrpCat.{w}) where
  X₁ := (F.op ⋙ extFunctor n).flip.obj A
  X₂ := H₁.op ⋙ (G.op ⋙ extFunctor n).flip.obj B
  X₃ := (H₁ ⋙ H₂).op ⋙ (K.op ⋙ extFunctor n).flip.obj C
  X₄ := (H₁ ⋙ H₂).op ⋙ (K.op ⋙ extFunctor n).flip.obj C
  f₁₂ := L₁.extDiagramMap F (H₁ ⋙ G) e₁ a n
  f₁₃ := L₀.extDiagramMap F ((H₁ ⋙ H₂) ⋙ K) e₀
    (c.hom.app A ≫ L₂.map a ≫ b) n
  f₂₄ := whiskerLeft H₁.op (L₂.extDiagramMap G (H₂ ⋙ K) e₂ b n)
  f₃₄ := 𝟙 _
  fac := by
    rw [Category.comp_id]
    exact L₁.extDiagramMap_comp L₂ L₀ c F G K H₁ H₂ e₁ e₂ e₀ hs a b n

/-- The complete original triangle law, with the identity edge eliminated
before supplying any native sheaf categories or coefficient objects. -/
theorem extDiagramCompositionSquare_comp
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
    (extDiagramCompositionSquare L₁ L₂ L₀ c F G K H₁ H₂ e₁ e₂ e₀ hs a b n).f₁₂ ≫
        (extDiagramCompositionSquare L₁ L₂ L₀ c F G K H₁ H₂ e₁ e₂ e₀ hs a b n).f₂₄ =
      (extDiagramCompositionSquare L₁ L₂ L₀ c F G K H₁ H₂ e₁ e₂ e₀ hs a b n).f₁₃ :=
  L₁.extDiagramMap_comp L₂ L₀ c F G K H₁ H₂ e₁ e₂ e₀ hs a b n

/-- The same complete triangle law at each original index object. -/
theorem extDiagramCompositionSquare_comp_app
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
    {A : C₀} {B : C₁} {C : C₂} (a : L₁.obj A ⟶ B) (b : L₂.obj B ⟶ C) (n : ℕ)
    (U : I₀ᵒᵖ) :
    (extDiagramCompositionSquare L₁ L₂ L₀ c F G K H₁ H₂ e₁ e₂ e₀ hs a b n).f₁₂.app U ≫
        (extDiagramCompositionSquare L₁ L₂ L₀ c F G K H₁ H₂ e₁ e₂ e₀ hs a b n).f₂₄.app U =
      (extDiagramCompositionSquare L₁ L₂ L₀ c F G K H₁ H₂ e₁ e₂ e₀ hs a b n).f₁₃.app U :=
  congrArg (fun t => t.app U)
    (extDiagramCompositionSquare_comp L₁ L₂ L₀ c F G K H₁ H₂ e₁ e₂ e₀ hs a b n)

end CategoryTheory.Functor
