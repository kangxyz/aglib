/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCompositionMap
public import Aglib.CategoryTheory.Functor.ImageInterchangeAssembly

/-! # The original left binary-composition route factors through the raw interchange -/

@[expose] public section
namespace CategoryTheory
variable {D A₀ A₁ A₂ B Y Z C E : Type*}
  [Category* D] [Category* A₀] [Category* A₁] [Category* A₂]
  [Category* B] [Category* Y] [Category* Z] [Category* C] [Category* E]
  {K : D ⥤ A₀} {J₁ : D ⥤ A₁} {J₂ : D ⥤ A₂}
  {Q₀ : A₀ ⥤ Y} {I₁ : Y ⥤ B} {M : A₀ ⥤ A₁} {R : A₁ ⥤ B}
  {Q₁ : B ⥤ Z} {I₂ : Z ⥤ C} {N : A₁ ⥤ A₂}
  {Vsrc : A₁ ⥤ Z} {Vtgt : A₂ ⥤ C} {P : C ⥤ E} {S : A₂ ⥤ E}
  (σa : Q₀ ⋙ I₁ ⟶ M ⋙ R) (σv : Vsrc ⋙ I₂ ⟶ N ⋙ Vtgt)
  (dv : Vsrc ≅ R ⋙ Q₁) (c₁ : K ⋙ M ≅ J₁) (c₂ : J₁ ⋙ N ≅ J₂)
  (s : Vtgt ⋙ P ≅ S)

/-- This is the actual composite of the two specified binary maps. -/
def imageLeftRoute : K ⋙ Q₀ ⋙ I₁ ⋙ Q₁ ⋙ I₂ ⋙ P ⟶ J₂ ⋙ S :=
  Functor.whiskerRight (imageCompositionMap σa c₁ dv.symm) (I₂ ⋙ P) ≫
    imageCompositionMap σv c₂ s

/-- The original open contractions appear only after the raw interchange. -/
def ImageLeftRouteEquation
    (α : K ⋙ Q₀ ⋙ I₁ ⋙ Q₁ ⋙ I₂ ⋙ P ⟶ J₂ ⋙ S) : Prop :=
  ∀ X, α.app X =
    P.map (I₂.map (Q₁.map (σa.app (K.obj X))) ≫
      I₂.map (dv.inv.app (M.obj (K.obj X))) ≫ σv.app (M.obj (K.obj X))) ≫
    P.map (Vtgt.map (N.map (c₁.hom.app X))) ≫
    P.map (Vtgt.map (c₂.hom.app X)) ≫ s.hom.app (J₂.obj X)

/-- Only naturality of the original proper compositor and interchange is used. -/
theorem imageLeftRouteEquation :
    ImageLeftRouteEquation σa σv dv c₁ c₂ s (imageLeftRoute σa σv dv c₁ c₂ s) := by
  intro X
  have hd := dv.inv.naturality (c₁.hom.app X)
  have hv := σv.naturality (c₁.hom.app X)
  change Q₁.map (R.map (c₁.hom.app X)) ≫ dv.inv.app (J₁.obj X) =
    dv.inv.app (M.obj (K.obj X)) ≫ Vsrc.map (c₁.hom.app X) at hd
  change I₂.map (Vsrc.map (c₁.hom.app X)) ≫ σv.app (J₁.obj X) =
    σv.app (M.obj (K.obj X)) ≫ Vtgt.map (N.map (c₁.hom.app X)) at hv
  have hd' := congrArg (fun z => P.map (I₂.map z)) hd
  have hv' := congrArg (fun z => P.map z) hv
  simp only [Functor.map_comp] at hd' hv'
  simp only [imageLeftRoute, imageCompositionMap, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
    Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [← Category.assoc (P.map (I₂.map (Q₁.map (R.map (c₁.hom.app X))))), hd']
  simp only [Category.assoc]
  rw [← Category.assoc (P.map (I₂.map (Vsrc.map (c₁.hom.app X)))), hv']
  simp only [Category.assoc]

end CategoryTheory
