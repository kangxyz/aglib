/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageLeftRoute
public import Aglib.CategoryTheory.Functor.ImageRightRoute
public import Aglib.CategoryTheory.Functor.OpenCompositionCoherence

/-! # Associativity of specified binary image maps from original interchange and compositors -/

@[expose] public section
namespace CategoryTheory
variable {D A₀ A₁ A₂ B₀ B₁ Y Z C E : Type*}
  [Category* D] [Category* A₀] [Category* A₁] [Category* A₂]
  [Category* B₀] [Category* B₁] [Category* Y] [Category* Z] [Category* C] [Category* E]
  {K : D ⥤ A₀} {J₁ : D ⥤ A₁} {J₂ : D ⥤ A₂}
  {Q₀ : A₀ ⥤ Y} {I₁ : Y ⥤ B₀} {M : A₀ ⥤ A₁} {R : A₁ ⥤ B₀}
  {Q₁ : B₀ ⥤ Z} {I₂ : Z ⥤ C} {M₁₂ : B₀ ⥤ B₁} {R₁₂ : B₁ ⥤ C}
  {N : A₁ ⥤ A₂} {R₀₂ : A₂ ⥤ B₁}
  {Vsrc : A₁ ⥤ Z} {Vtgt : A₂ ⥤ C} {Hsrc : Y ⥤ B₁} {Htgt : A₀ ⥤ A₂}
  {P : C ⥤ E} {Stail : B₁ ⥤ E} {S : A₂ ⥤ E}
  (σa : Q₀ ⋙ I₁ ⟶ M ⋙ R) (σb : Q₁ ⋙ I₂ ⟶ M₁₂ ⋙ R₁₂)
  (σv : Vsrc ⋙ I₂ ⟶ N ⋙ Vtgt) (σh : Q₀ ⋙ Hsrc ⟶ Htgt ⋙ R₀₂)
  (dv : Vsrc ≅ R ⋙ Q₁) (ev : Vtgt ≅ R₀₂ ⋙ R₁₂)
  (dh : Hsrc ≅ I₁ ⋙ M₁₂) (eh : Htgt ≅ M ⋙ N)
  (c₁ : K ⋙ M ≅ J₁) (c₂ : J₁ ⋙ N ≅ J₂) (cR : K ⋙ Htgt ≅ J₂)
  (sL : Vtgt ⋙ P ≅ S) (sTail : R₁₂ ⋙ P ≅ Stail) (sR : R₀₂ ⋙ Stail ≅ S)

/-- Original horizontal/vertical interchange and the two original compositor laws suffice. -/
theorem imageTripleComposition
    (hi : ImageInterchangeAssociativityEquation σa σb σv σh dv ev dh eh)
    (hJ : OpenCompositionEquation c₁ c₂ cR eh.symm)
    (hR : OpenCompositionEquation ev.symm sL sR sTail) :
    imageLeftRoute σa σv dv c₁ c₂ sL = imageRightRoute σb σh dh cR sTail sR := by
  apply NatTrans.ext
  funext X
  have hj := congrArg (fun e => e.hom.app X) hJ
  change N.map (c₁.hom.app X) ≫ c₂.hom.app X =
    𝟙 _ ≫ eh.inv.app (K.obj X) ≫ cR.hom.app X at hj
  simp only [Category.id_comp] at hj
  have hr := congrArg (fun e => e.hom.app (J₂.obj X)) hR
  change P.map (ev.inv.app (J₂.obj X)) ≫ sL.hom.app (J₂.obj X) =
    𝟙 _ ≫ sTail.hom.app (R₀₂.obj (J₂.obj X)) ≫ sR.hom.app (J₂.obj X) at hr
  simp only [Category.id_comp] at hr
  have hr' : sL.hom.app (J₂.obj X) = P.map (ev.hom.app (J₂.obj X)) ≫
      sTail.hom.app (R₀₂.obj (J₂.obj X)) ≫ sR.hom.app (J₂.obj X) := by
    rw [← hr]
    simp only [← Category.assoc, ← P.map_comp, Iso.hom_inv_id_app, P.map_id,
      Category.id_comp]
  have hn := ev.hom.naturality (N.map (c₁.hom.app X) ≫ c₂.hom.app X)
  change Vtgt.map (N.map (c₁.hom.app X) ≫ c₂.hom.app X) ≫
      ev.hom.app (J₂.obj X) =
    ev.hom.app (N.obj (M.obj (K.obj X))) ≫
      R₁₂.map (R₀₂.map (N.map (c₁.hom.app X) ≫ c₂.hom.app X)) at hn
  have hn' := congrArg (fun z => P.map z) hn
  simp only [Functor.map_comp, Category.assoc] at hn'
  rw [imageLeftRouteEquation σa σv dv c₁ c₂ sL X,
    imageRightRouteEquation σb σh dh cR sTail sR X, hr']
  simp only [Functor.map_comp, Category.assoc]
  have hnTail := congrArg
    (fun z => z ≫ sTail.hom.app (R₀₂.obj (J₂.obj X)) ≫ sR.hom.app (J₂.obj X)) hn'
  simp only [Category.assoc] at hnTail
  rw [hnTail]
  have hi' := congrArg (fun z => P.map z) (hi (K.obj X))
  simp only [Functor.map_comp] at hi'
  have hiTail := congrArg
    (fun z => z ≫ P.map (R₁₂.map (R₀₂.map (N.map (c₁.hom.app X)))) ≫
      P.map (R₁₂.map (R₀₂.map (c₂.hom.app X))) ≫
      sTail.hom.app (R₀₂.obj (J₂.obj X)) ≫ sR.hom.app (J₂.obj X)) hi'
  simp only [Category.assoc] at hiTail
  rw [hiTail]
  have hj' := congrArg (fun z => P.map (R₁₂.map (R₀₂.map z))) hj
  simp only [Functor.map_comp] at hj'
  have hjTail := congrArg
    (fun z => z ≫ sTail.hom.app (R₀₂.obj (J₂.obj X)) ≫ sR.hom.app (J₂.obj X)) hj'
  simp only [Category.assoc] at hjTail
  rw [hjTail]
  have he := congrArg (fun z => P.map (R₁₂.map (R₀₂.map z)))
    (eh.hom_inv_id_app (K.obj X))
  simp only [Functor.map_comp, Functor.map_id] at he
  have heTail := congrArg
    (fun z => z ≫ P.map (R₁₂.map (R₀₂.map (cR.hom.app X))) ≫
      sTail.hom.app (R₀₂.obj (J₂.obj X)) ≫ sR.hom.app (J₂.obj X)) he
  simp only [Category.assoc, Category.id_comp] at heTail
  rw [heTail]

end CategoryTheory
