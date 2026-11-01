/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Whiskering

/-!
# Pasting original comparisons with their target-image identifications

This categorical calculation retains the actual transformations and specified
isomorphisms. It is independent of schemes, derived models and torsion. The
compactification diagram specializes it to the original refinement comparison
and structural direct-image composition; no coherence is replaced by an input
without proving that input from the existing original maps.
-/

@[expose] public noncomputable section

namespace CategoryTheory

variable {U A B C T : Type*}
  [Category* U] [Category* A] [Category* B] [Category* C] [Category* T]

/-- Postcompose an original comparison and identify its target through the
specified structural-image isomorphism. -/
def imageComparison {L₁ : U ⥤ A} {L₂ : U ⥤ B} {R₁ : A ⥤ T} {R₂ : B ⥤ T}
    {F : A ⥤ B} (δ : L₂ ⟶ L₁ ⋙ F) (e : F ⋙ R₂ ≅ R₁) :
    L₂ ⋙ R₂ ⟶ L₁ ⋙ R₁ :=
  Functor.whiskerRight δ R₂ ≫ (Functor.associator L₁ F R₂).hom ≫
    Functor.whiskerLeft L₁ e.hom

/-- The pasted component uses the same original component and target identification. -/
theorem imageComparison_app {L₁ : U ⥤ A} {L₂ : U ⥤ B}
    {R₁ : A ⥤ T} {R₂ : B ⥤ T} {F : A ⥤ B}
    (δ : L₂ ⟶ L₁ ⋙ F) (e : F ⋙ R₂ ≅ R₁) (K : U) :
    (imageComparison δ e).app K = R₂.map (δ.app K) ≫ e.hom.app (L₁.obj K) := by
  simp only [imageComparison, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp]

/-- A normalized original identity comparison pastes to the identity. -/
theorem imageComparison_id {L : U ⥤ A} {R : A ⥤ T} {F : A ⥤ A}
    (δ : L ⟶ L ⋙ F) (d : F ≅ 𝟭 A) (e : F ⋙ R ≅ R)
    (hδ : δ ≫ Functor.whiskerLeft L d.hom ≫ (Functor.rightUnitor L).hom = 𝟙 L)
    (he : e = Functor.isoWhiskerRight d R ≪≫ Functor.leftUnitor R) :
    imageComparison δ e = 𝟙 (L ⋙ R) := by
  subst e
  apply NatTrans.ext
  funext K
  have h := congrArg (fun τ : L ⟶ L => τ.app K) hδ
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    Category.comp_id, NatTrans.id_app] at h
  simp only [imageComparison_app, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.comp_obj, Functor.id_obj, Category.comp_id, NatTrans.id_app]
  rw [← R.map_comp, h, R.map_id]

/-- Original comparison composition and structural-image coherence imply the
contravariant composition law for the pasted comparisons. -/
theorem imageComparison_comp
    {L₁ : U ⥤ A} {L₂ : U ⥤ B} {L₃ : U ⥤ C}
    {R₁ : A ⥤ T} {R₂ : B ⥤ T} {R₃ : C ⥤ T}
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    (δ₁₂ : L₂ ⟶ L₁ ⋙ F) (δ₂₃ : L₃ ⟶ L₂ ⋙ G) (δ₁₃ : L₃ ⟶ L₁ ⋙ H)
    (c : H ≅ F ⋙ G) (e₁₂ : F ⋙ R₂ ≅ R₁)
    (e₂₃ : G ⋙ R₃ ≅ R₂) (e₁₃ : H ⋙ R₃ ≅ R₁)
    (hδ : δ₁₃ ≫ Functor.whiskerLeft L₁ c.hom =
      δ₂₃ ≫ Functor.whiskerRight δ₁₂ G ≫ (Functor.associator L₁ F G).hom)
    (he : Functor.isoWhiskerLeft F e₂₃ ≪≫ e₁₂ =
      (Functor.associator F G R₃).symm ≪≫
        Functor.isoWhiskerRight c.symm R₃ ≪≫ e₁₃) :
    imageComparison δ₁₃ e₁₃ = imageComparison δ₂₃ e₂₃ ≫ imageComparison δ₁₂ e₁₂ := by
  apply NatTrans.ext
  funext K
  have hδK := congrArg (fun τ : L₃ ⟶ L₁ ⋙ F ⋙ G => τ.app K) hδ
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id] at hδK
  have heK := congrArg (fun e : F ⋙ G ⋙ R₃ ≅ R₁ => e.hom.app (L₁.obj K)) he
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp] at heK
  have ht : e₁₃.hom.app (L₁.obj K) = R₃.map (c.hom.app (L₁.obj K)) ≫
      e₂₃.hom.app (F.obj (L₁.obj K)) ≫ e₁₂.hom.app (L₁.obj K) := by
    rw [heK]
    simp only [← Category.assoc, ← R₃.map_comp, Iso.hom_inv_id_app,
      R₃.map_id, Category.id_comp]
  simp only [imageComparison_app, NatTrans.comp_app]
  rw [ht, ← Category.assoc, ← R₃.map_comp, hδK, R₃.map_comp]
  simpa only [Functor.comp_map, Functor.comp_obj, Category.assoc] using
    congrArg (fun t => R₃.map (δ₂₃.app K) ≫ t ≫ e₁₂.hom.app (L₁.obj K))
      (e₂₃.hom.naturality (δ₁₂.app K))

/-- If the original comparison component is invertible, so is its pasted image. -/
theorem imageComparison_isIso_app {L₁ : U ⥤ A} {L₂ : U ⥤ B}
    {R₁ : A ⥤ T} {R₂ : B ⥤ T} {F : A ⥤ B}
    (δ : L₂ ⟶ L₁ ⋙ F) (e : F ⋙ R₂ ≅ R₁) (K : U) [IsIso (δ.app K)] :
    IsIso ((imageComparison δ e).app K) := by
  rw [imageComparison_app]
  infer_instance

end CategoryTheory
