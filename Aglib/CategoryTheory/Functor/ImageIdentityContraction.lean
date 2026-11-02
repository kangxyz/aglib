/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import
  Aglib.CategoryTheory.Functor.ImageComparison
/-! # Original image comparison followed by the original identity contraction -/
@[expose] public noncomputable section
open CategoryTheory.Functor
namespace CategoryTheory
variable {E M : Type*} [Category* E] [Category* M]
  {J S : E ⥤ M} {J₀ I : E ⥤ E} {R : M ⥤ E}

/-- The original outer-adjoint comparison normalizes the original identity image transition. -/
theorem imageComparison_identityContraction
    (δ : J ⟶ J₀ ⋙ S) (t : S ⋙ R ≅ I) (j : J₀ ≅ 𝟭 E) (i : I ≅ 𝟭 E)
    (b : J ⟶ S) (ε : J ⋙ R ≅ 𝟭 E)
    (hb : δ ≫ whiskerRight j.hom S ≫ (leftUnitor S).hom = b)
    (hε : whiskerRight b R ≫ (t ≪≫ i).hom = ε.hom) :
    imageComparison δ t ≫ (isoWhiskerRight j I ≪≫ leftUnitor I ≪≫ i).hom = ε.hom := by
  ext K
  have h₁ := congr_app hb K
  have h₂ := congr_app hε K
  have hn := t.hom.naturality (j.hom.app K)
  simp only [NatTrans.comp_app, whiskerRight_app, leftUnitor_hom_app] at h₁
  have hiS := Category.comp_id (S.map (j.hom.app K))
  dsimp only [Functor.id_obj] at hiS
  rw [hiS] at h₁
  simp only [NatTrans.comp_app, whiskerRight_app, Iso.trans_hom] at h₂
  dsimp only [Functor.comp_map, Functor.id_obj] at hn
  simp only [NatTrans.comp_app, imageComparison_app, Iso.trans_hom,
    isoWhiskerRight_hom, whiskerRight_app, leftUnitor_hom_app, Category.assoc]
  have hiI := Category.id_comp (i.hom.app K)
  rw [hiI, ← reassoc_of% hn, ← R.map_comp_assoc, h₁]
  exact h₂
end CategoryTheory
