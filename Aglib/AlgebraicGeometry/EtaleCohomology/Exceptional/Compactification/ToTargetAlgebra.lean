/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Functor.ImageComparison

/-! # Pasting a comparison square with a structural triangle -/
@[expose] public noncomputable section
namespace CategoryTheory
variable {U A B T : Type*} [Category* U] [Category* A] [Category* B] [Category* T]
  {L₁ S₁ : U ⥤ A} {L₂ S₂ : U ⥤ B} {R₁ : A ⥤ T} {R₂ : B ⥤ T}
  {F : A ⥤ B} {H : U ⥤ T}

/-- A structural triangle transports an original comparison square to the target. -/
theorem imageComparison_toTarget
    (δ : L₂ ⟶ L₁ ⋙ F) (b₁ : L₁ ⟶ S₁) (b₂ : L₂ ⟶ S₂)
    (c : S₁ ⋙ F ≅ S₂) (e : F ⋙ R₂ ≅ R₁)
    (t₁ : S₁ ⋙ R₁ ≅ H) (t₂ : S₂ ⋙ R₂ ≅ H)
    (hδ : ∀ K, δ.app K ≫ F.map (b₁.app K) ≫ c.hom.app K = b₂.app K)
    (ht : Functor.isoWhiskerLeft S₁ e ≪≫ t₁ =
      (Functor.associator S₁ F R₂).symm ≪≫ Functor.isoWhiskerRight c R₂ ≪≫ t₂) :
    imageComparison δ e ≫ Functor.whiskerRight b₁ R₁ ≫ t₁.hom =
      Functor.whiskerRight b₂ R₂ ≫ t₂.hom := by
  apply NatTrans.ext
  funext K
  have h := congrArg (fun i => i.hom.app K) ht
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] at h
  simp only [NatTrans.comp_app, imageComparison_app, Functor.whiskerRight_app]
  rw [Category.assoc, ← e.hom.naturality_assoc, h]
  simpa only [Functor.comp_map, Category.assoc, R₂.map_comp] using
    congrArg (fun z => R₂.map z ≫ t₂.hom.app K) (hδ K)
end CategoryTheory
