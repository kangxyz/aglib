/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageRightRoute
public import Aglib.CategoryTheory.Functor.ImageCompositionTarget
public import Aglib.CategoryTheory.Functor.ImageRightOpenTransport

/-! # The original right route retains the actual middle-open equality transport -/

@[expose] public section
namespace CategoryTheory
variable {D A₀ A₂ B₀ B₁ Y Z C E : Type*}
  [Category* D] [Category* A₀] [Category* A₂] [Category* B₀] [Category* B₁]
  [Category* Y] [Category* Z] [Category* C] [Category* E]
  {K : D ⥤ A₀} {J : D ⥤ A₂} {Q₀ : A₀ ⥤ Y} {I₁ : Y ⥤ B₀}
  {Q₁ : B₀ ⥤ Z} {I₂ : Z ⥤ C} {M : B₀ ⥤ B₁} {R : B₁ ⥤ C}
  {Hsrc Hsrc' : Y ⥤ B₁} {Htgt : A₀ ⥤ A₂} {R₀₂ : A₂ ⥤ B₁}
  {P : C ⥤ E} {Stail : B₁ ⥤ E} {S S' : A₂ ⥤ E}

/-- Whole original right-route realization, with its actual two maps kept opaque. -/
def ImageRightRealizationEquation
    (σb : Q₁ ⋙ I₂ ⟶ M ⋙ R) (σh : Q₀ ⋙ Hsrc ⟶ Htgt ⋙ R₀₂)
    (dh : Hsrc ≅ I₁ ⋙ M) (c : K ⋙ Htgt ≅ J)
    (sTail : R ⋙ P ≅ Stail) (s : R₀₂ ⋙ Stail ≅ S) (ep : S ≅ S')
    (αtail : I₁ ⋙ Q₁ ⋙ I₂ ⋙ P ⟶ Hsrc' ⋙ Stail)
    (αouter : K ⋙ Q₀ ⋙ Hsrc' ⋙ Stail ⟶ J ⋙ S) : Prop :=
  Functor.whiskerLeft (K ⋙ Q₀) αtail ≫ αouter ≫ Functor.whiskerLeft J ep.hom =
    imageRightRoute σb σh dh c sTail (s ≪≫ ep)

/-- Original map formulas and the original open transport produce the same whole predicate. -/
theorem imageRightRealizationEquation
    (σb : Q₁ ⋙ I₂ ⟶ M ⋙ R) (σh : Q₀ ⋙ Hsrc ⟶ Htgt ⋙ R₀₂)
    (σh' : Q₀ ⋙ Hsrc' ⟶ Htgt ⋙ R₀₂)
    (dh : Hsrc ≅ I₁ ⋙ M) (e : Hsrc ≅ Hsrc')
    (he : σh = Functor.whiskerLeft Q₀ e.hom ≫ σh')
    (c : K ⋙ Htgt ≅ J) (sTail : R ⋙ P ≅ Stail)
    (s : R₀₂ ⋙ Stail ≅ S) (ep : S ≅ S')
    (αtail : I₁ ⋙ Q₁ ⋙ I₂ ⋙ P ⟶ Hsrc' ⋙ Stail)
    (αouter : K ⋙ Q₀ ⋙ Hsrc' ⋙ Stail ⟶ J ⋙ S)
    (hTail : αtail = imageCompositionMap σb (dh.symm ≪≫ e) sTail)
    (hOuter : αouter = imageCompositionMap σh' c s) :
    ImageRightRealizationEquation σb σh dh c sTail s ep αtail αouter := by
  subst αtail
  subst αouter
  have ht := imageRightRoute_open_transport σb σh σh' dh e he c sTail (s ≪≫ ep)
  rw [imageCompositionMap_change_target, ← Category.assoc] at ht
  simpa only [ImageRightRealizationEquation, Category.assoc] using ht

end CategoryTheory
