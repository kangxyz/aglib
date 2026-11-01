/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageTripleComposition

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

/-- Both original binary routes, kept as one regular native specialization boundary. -/
def ImageTripleCompositionEquation : Prop :=
  imageLeftRoute σa σv dv c₁ c₂ sL = imageRightRoute σb σh dh cR sTail sR

/-- The original interchange and contraction laws produce that exact whole equation. -/
theorem imageTripleCompositionEquation
    (hi : ImageInterchangeAssociativityEquation σa σb σv σh dv ev dh eh)
    (hJ : OpenCompositionEquation c₁ c₂ cR eh.symm)
    (hR : OpenCompositionEquation ev.symm sL sR sTail) :
    ImageTripleCompositionEquation σa σb σv σh dv dh c₁ c₂ cR sL sTail sR :=
  imageTripleComposition σa σb σv σh dv ev dh eh c₁ c₂ cR sL sTail sR hi hJ hR

end CategoryTheory
