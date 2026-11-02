/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCompositionMap

/-! # The original right binary-composition route factors through the raw interchange -/

@[expose] public section
namespace CategoryTheory
variable {D A₀ A₂ B₀ B₁ Y Z C E : Type*}
  [Category* D] [Category* A₀] [Category* A₂] [Category* B₀] [Category* B₁]
  [Category* Y] [Category* Z] [Category* C] [Category* E]
  {K : D ⥤ A₀} {J : D ⥤ A₂} {Q₀ : A₀ ⥤ Y} {I₁ : Y ⥤ B₀}
  {Q₁ : B₀ ⥤ Z} {I₂ : Z ⥤ C} {M : B₀ ⥤ B₁} {R : B₁ ⥤ C}
  {Hsrc : Y ⥤ B₁} {Htgt : A₀ ⥤ A₂} {R₀₂ : A₂ ⥤ B₁}
  {P : C ⥤ E} {Stail : B₁ ⥤ E} {S : A₂ ⥤ E}
  (σb : Q₁ ⋙ I₂ ⟶ M ⋙ R) (σh : Q₀ ⋙ Hsrc ⟶ Htgt ⋙ R₀₂)
  (dh : Hsrc ≅ I₁ ⋙ M) (c : K ⋙ Htgt ≅ J)
  (sTail : R ⋙ P ≅ Stail) (s : R₀₂ ⋙ Stail ≅ S)

/-- The specified two binary maps, without changing either original compositor. -/
def imageRightRoute : K ⋙ Q₀ ⋙ I₁ ⋙ Q₁ ⋙ I₂ ⋙ P ⟶ J ⋙ S :=
  Functor.whiskerLeft (K ⋙ Q₀) (imageCompositionMap σb dh.symm sTail) ≫
    imageCompositionMap σh c s

/-- The original proper contractions occur after the raw horizontal interchange. -/
def ImageRightRouteEquation
    (α : K ⋙ Q₀ ⋙ I₁ ⋙ Q₁ ⋙ I₂ ⋙ P ⟶ J ⋙ S) : Prop :=
  ∀ X, α.app X =
    P.map (σb.app (I₁.obj (Q₀.obj (K.obj X))) ≫
      R.map (dh.inv.app (Q₀.obj (K.obj X))) ≫ R.map (σh.app (K.obj X))) ≫
    P.map (R.map (R₀₂.map (c.hom.app X))) ≫
    sTail.hom.app (R₀₂.obj (J.obj X)) ≫ s.hom.app (J.obj X)

/-- Naturality moves the same original proper compositor past the specified maps. -/
theorem imageRightRouteEquation :
    ImageRightRouteEquation σb σh dh c sTail s
      (imageRightRoute σb σh dh c sTail s) := by
  intro X
  have hs := sTail.hom.naturality (σh.app (K.obj X))
  have hc := sTail.hom.naturality (R₀₂.map (c.hom.app X))
  change P.map (R.map (σh.app (K.obj X))) ≫
      sTail.hom.app (R₀₂.obj (Htgt.obj (K.obj X))) =
    sTail.hom.app (Hsrc.obj (Q₀.obj (K.obj X))) ≫
      Stail.map (σh.app (K.obj X)) at hs
  change P.map (R.map (R₀₂.map (c.hom.app X))) ≫
      sTail.hom.app (R₀₂.obj (J.obj X)) =
    sTail.hom.app (R₀₂.obj (Htgt.obj (K.obj X))) ≫
      Stail.map (R₀₂.map (c.hom.app X)) at hc
  simp only [imageRightRoute, imageCompositionMap, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
    Functor.comp_obj, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [← Category.assoc (sTail.hom.app (Hsrc.obj (Q₀.obj (K.obj X)))), ← hs]
  simp only [Category.assoc]
  rw [← Category.assoc (sTail.hom.app (R₀₂.obj (Htgt.obj (K.obj X)))), ← hc]
  simp only [Category.assoc]

end CategoryTheory
