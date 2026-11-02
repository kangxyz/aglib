/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageInterchangeAssociativity

/-! # Assemble actual triple image maps from their original route formulas

The input formulas expose only the original preMap/postMap comparisons and
actual interchange routes. The interchange equality is proved independently
from the original horizontal and vertical laws, not assumed as a desired
associativity field of a compactification object.
-/

@[expose] public section
namespace CategoryTheory

variable {A₀ A₁ A₂ B₀ B₁ Y Z C : Type*}
  [Category* A₀] [Category* A₁] [Category* A₂] [Category* B₀] [Category* B₁]
  [Category* Y] [Category* Z] [Category* C]
  {Q₀ : A₀ ⥤ Y} {I₁ : Y ⥤ B₀} {M₀₁ : A₀ ⥤ A₁} {R₀₁ : A₁ ⥤ B₀}
  {Q₁ : B₀ ⥤ Z} {I₂ : Z ⥤ C} {M₁₂ : B₀ ⥤ B₁} {R₁₂ : B₁ ⥤ C}
  {N : A₁ ⥤ A₂} {R₀₂ : A₂ ⥤ B₁}
  {Vsrc : A₁ ⥤ Z} {Vtgt : A₂ ⥤ C} {Hsrc : Y ⥤ B₁} {Htgt : A₀ ⥤ A₂}
  (σa : Q₀ ⋙ I₁ ⟶ M₀₁ ⋙ R₀₁)
  (σb : Q₁ ⋙ I₂ ⟶ M₁₂ ⋙ R₁₂)
  (σv : Vsrc ⋙ I₂ ⟶ N ⋙ Vtgt) (σh : Q₀ ⋙ Hsrc ⟶ Htgt ⋙ R₀₂)
  (dv : Vsrc ≅ R₀₁ ⋙ Q₁) (ev : Vtgt ≅ R₀₂ ⋙ R₁₂)
  (dh : Hsrc ≅ I₁ ⋙ M₁₂) (eh : Htgt ≅ M₀₁ ⋙ N)


variable {D E : Type*} [Category* D] [Category* E]
  (K : D ⥤ A₀) (P : C ⥤ E) {F G : D ⥤ E}
  (preMap : F ⟶ K ⋙ Q₀ ⋙ I₁ ⋙ Q₁ ⋙ I₂ ⋙ P)
  (postMap : K ⋙ M₀₁ ⋙ N ⋙ R₀₂ ⋙ R₁₂ ⋙ P ⟶ G)
  (αL αR : F ⟶ G)

/-- The specified left route retains the original maps and endpoint comparisons. -/
def ImageInterchangeLeftFormula : Prop :=
  ∀ X, αL.app X = preMap.app X ≫ P.map
    (I₂.map (Q₁.map (σa.app (K.obj X))) ≫
      I₂.map (dv.inv.app (M₀₁.obj (K.obj X))) ≫ σv.app (M₀₁.obj (K.obj X)) ≫
      ev.hom.app (N.obj (M₀₁.obj (K.obj X)))) ≫ postMap.app X

/-- The specified right route retains the same original endpoint comparisons. -/
def ImageInterchangeRightFormula : Prop :=
  ∀ X, αR.app X = preMap.app X ≫ P.map
    (σb.app (I₁.obj (Q₀.obj (K.obj X))) ≫ R₁₂.map (dh.inv.app (Q₀.obj (K.obj X))) ≫
      R₁₂.map (σh.app (K.obj X)) ≫ R₁₂.map (R₀₂.map (eh.hom.app (K.obj X)))) ≫ postMap.app X

/-- Original route formulas and proved interchange identify the actual complete maps. -/
theorem imageInterchangeAssembly
    (hc : ImageInterchangeAssociativityEquation σa σb σv σh dv ev dh eh)
    (hL : ImageInterchangeLeftFormula σa σv dv ev K P preMap postMap αL)
    (hR : ImageInterchangeRightFormula σb σh dh eh K P preMap postMap αR) :
    αL = αR := by
  apply NatTrans.ext
  funext X
  rw [hL, hR, hc]

end CategoryTheory
