/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.UnitMateHorizontal
public import Aglib.CategoryTheory.Adjunction.NaturalPastedRectangleSource

/-! # Pasting the original horizontal and vertical refinement faces

All maps and compositors are specified. Naturality and the three original face
equations imply the resulting image-composition cube. No comparison is chosen
from an assertion that its endpoints are isomorphic.
-/

@[expose] public section

namespace CategoryTheory

variable {A B₀ B₁ C₀ C₁ M N₀ N₁ Z : Type*}
  [Category* A] [Category* B₀] [Category* B₁] [Category* C₀] [Category* C₁]
  [Category* M] [Category* N₀] [Category* N₁] [Category* Z]
  {K₀ : A ⥤ B₀} {K₁ : A ⥤ B₁} {J₀ : A ⥤ C₀} {J₁ : A ⥤ C₁}
  {L₀ : B₀ ⥤ C₀} {L₁ : B₁ ⥤ C₁} {I₀ : M ⥤ N₀} {I₁ : M ⥤ N₁}
  {Q₀ : B₀ ⥤ M} {Q₁ : B₁ ⥤ M} {R₀ : C₀ ⥤ N₀} {R₁ : C₁ ⥤ N₁}
  {P₀ : N₀ ⥤ Z} {P₁ : N₁ ⥤ Z} {S₀ : C₀ ⥤ Z} {S₁ : C₁ ⥤ Z}
  {F : B₁ ⥤ B₀} {G : C₁ ⥤ C₀} {H : N₁ ⥤ N₀}
  (δK : K₀ ⟶ K₁ ⋙ F) (δI : I₀ ⟶ I₁ ⋙ H) (δJ : J₀ ⟶ J₁ ⋙ G)
  (σ₀ : Q₀ ⋙ I₀ ⟶ L₀ ⋙ R₀) (σ₁ : Q₁ ⋙ I₁ ⟶ L₁ ⋙ R₁)
  (σ : F ⋙ L₀ ⟶ L₁ ⋙ G)
  (c₀ : K₀ ⋙ L₀ ≅ J₀) (c₁ : K₁ ⋙ L₁ ≅ J₁)
  (q : F ⋙ Q₀ ≅ Q₁) (p : H ⋙ P₀ ≅ P₁) (r : R₁ ⋙ H ≅ G ⋙ R₀)
  (s₀ : R₀ ⋙ P₀ ≅ S₀) (s₁ : R₁ ⋙ P₁ ≅ S₁) (t : G ⋙ S₀ ≅ S₁)

/-- The original structural-image face, retained as a typed equation. -/
def ImageCompositionStructuralEquation : Prop :=
  ∀ C, p.hom.app (R₁.obj C) ≫ s₁.hom.app C =
    P₀.map (r.hom.app C) ≫ s₀.hom.app (G.obj C) ≫ t.hom.app C

/-- The literal component equation for the original image-composition cube. -/
def ImageCompositionRefinementEquation : Prop :=
  ∀ K,
    P₀.map (I₀.map (Q₀.map (δK.app K) ≫ q.hom.app (K₁.obj K))) ≫
      P₀.map (δI.app (Q₁.obj (K₁.obj K))) ≫ p.hom.app (I₁.obj (Q₁.obj (K₁.obj K))) ≫
      P₁.map (σ₁.app (K₁.obj K)) ≫ P₁.map (R₁.map (c₁.hom.app K)) ≫ s₁.hom.app (J₁.obj K) =
    P₀.map (σ₀.app (K₀.obj K)) ≫ P₀.map (R₀.map (c₀.hom.app K)) ≫ s₀.hom.app (J₀.obj K) ≫
      S₀.map (δJ.app K) ≫ t.hom.app (J₁.obj K)

/-- The three original face equations paste to the original whole image cube. -/
theorem imageCompositionRefinementEquation
    (hHorizontal : UnitMateHorizontalEquation δK δJ σ c₀.symm c₁.symm)
    (hRectangle : NaturalRefinementRectangleEquation σ₀ σ δI σ₁ q r)
    (hStructural : ImageCompositionStructuralEquation p r s₀ s₁ t) :
    ImageCompositionRefinementEquation δK δI δJ σ₀ σ₁ c₀ c₁ q p s₀ s₁ t := by
  intro K
  have hH : L₀.map (δK.app K) ≫ σ.app (K₁.obj K) ≫ G.map (c₁.hom.app K) =
      c₀.hom.app K ≫ δJ.app K := by
    have hh := congrArg (fun z => c₀.hom.app K ≫ z ≫ G.map (c₁.hom.app K))
      (hHorizontal K)
    simp only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id_app_assoc,
      ← G.map_comp, Iso.inv_hom_id_app, G.map_id] at hh
    exact hh.trans (congrArg (fun z => c₀.hom.app K ≫ z) (Category.comp_id (δJ.app K)))
  have hR : I₀.map (q.hom.app (K₁.obj K)) ≫
      δI.app (Q₁.obj (K₁.obj K)) ≫ H.map (σ₁.app (K₁.obj K)) ≫
        r.hom.app (L₁.obj (K₁.obj K)) =
      σ₀.app (F.obj (K₁.obj K)) ≫ R₀.map (σ.app (K₁.obj K)) := by
    have hh := congrArg (fun z => I₀.map (q.hom.app (K₁.obj K)) ≫ z)
      (hRectangle (K₁.obj K)).symm
    simpa only [Category.assoc, ← I₀.map_comp_assoc, Iso.hom_inv_id_app,
      I₀.map_id, Category.id_comp] using hh
  have hCore :
      I₀.map (Q₀.map (δK.app K) ≫ q.hom.app (K₁.obj K)) ≫
        δI.app (Q₁.obj (K₁.obj K)) ≫ H.map (σ₁.app (K₁.obj K)) ≫
        H.map (R₁.map (c₁.hom.app K)) ≫ r.hom.app (J₁.obj K) =
      σ₀.app (K₀.obj K) ≫ R₀.map (c₀.hom.app K) ≫ R₀.map (δJ.app K) := by
    have hn := r.hom.naturality (c₁.hom.app K)
    change H.map (R₁.map (c₁.hom.app K)) ≫ r.hom.app (J₁.obj K) =
      r.hom.app (L₁.obj (K₁.obj K)) ≫ R₀.map (G.map (c₁.hom.app K)) at hn
    rw [hn, I₀.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% hR]
    have hnσ := σ₀.naturality (δK.app K)
    change I₀.map (Q₀.map (δK.app K)) ≫ σ₀.app (F.obj (K₁.obj K)) =
      σ₀.app (K₀.obj K) ≫ R₀.map (L₀.map (δK.app K)) at hnσ
    rw [reassoc_of% hnσ]
    simpa only [Functor.comp_map, Functor.comp_obj, R₀.map_comp, Category.assoc] using
      congrArg (fun z => σ₀.app (K₀.obj K) ≫ R₀.map z) hH
  have hnP := p.hom.naturality
    (σ₁.app (K₁.obj K) ≫ R₁.map (c₁.hom.app K))
  have hnS := s₀.hom.naturality (δJ.app K)
  change P₀.map (H.map _) ≫ p.hom.app (R₁.obj (J₁.obj K)) =
    p.hom.app (I₁.obj (Q₁.obj (K₁.obj K))) ≫ P₁.map _ at hnP
  change P₀.map (R₀.map (δJ.app K)) ≫ s₀.hom.app (G.obj (J₁.obj K)) =
    s₀.hom.app (J₀.obj K) ≫ S₀.map (δJ.app K) at hnS
  rw [← P₁.map_comp_assoc, ← reassoc_of% hnP]
  rw [hStructural]
  simp only [← P₀.map_comp_assoc, H.map_comp, Category.assoc]
  rw [hCore]
  simp only [P₀.map_comp, Category.assoc]
  rw [reassoc_of% hnS]

end CategoryTheory
