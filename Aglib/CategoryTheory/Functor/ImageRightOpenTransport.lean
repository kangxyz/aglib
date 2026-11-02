/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageRightRoute
public import Aglib.CategoryTheory.Functor.ImageCompositionTransport

/-! # The original right route retains the actual middle-open equality transport -/

@[expose] public section
namespace CategoryTheory
variable {D A₀ A₂ B₀ B₁ Y Z C E : Type*}
  [Category* D] [Category* A₀] [Category* A₂] [Category* B₀] [Category* B₁]
  [Category* Y] [Category* Z] [Category* C] [Category* E]
  {K : D ⥤ A₀} {J : D ⥤ A₂} {Q₀ : A₀ ⥤ Y} {I₁ : Y ⥤ B₀}
  {Q₁ : B₀ ⥤ Z} {I₂ : Z ⥤ C} {M : B₀ ⥤ B₁} {R : B₁ ⥤ C}
  {Hsrc Hsrc' : Y ⥤ B₁} {Htgt : A₀ ⥤ A₂} {R₀₂ : A₂ ⥤ B₁}
  {P : C ⥤ E} {Stail : B₁ ⥤ E} {S : A₂ ⥤ E}

/-- Both occurrences of the specified middle-open comparison cancel by actual naturality. -/
theorem imageRightRoute_open_transport
    (σb : Q₁ ⋙ I₂ ⟶ M ⋙ R) (σh : Q₀ ⋙ Hsrc ⟶ Htgt ⋙ R₀₂)
    (σh' : Q₀ ⋙ Hsrc' ⟶ Htgt ⋙ R₀₂)
    (dh : Hsrc ≅ I₁ ⋙ M) (e : Hsrc ≅ Hsrc')
    (he : σh = Functor.whiskerLeft Q₀ e.hom ≫ σh')
    (c : K ⋙ Htgt ≅ J) (sTail : R ⋙ P ≅ Stail) (s : R₀₂ ⋙ Stail ≅ S) :
    Functor.whiskerLeft (K ⋙ Q₀) (imageCompositionMap σb (dh.symm ≪≫ e) sTail) ≫
        imageCompositionMap σh' c s =
      imageRightRoute σb σh dh c sTail s := by
  rw [imageCompositionMap_change_output]
  unfold imageRightRoute
  rw [imageCompositionMap_change_input σh σh' e.hom he]
  apply NatTrans.ext
  funext X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_obj, Category.assoc]

end CategoryTheory
