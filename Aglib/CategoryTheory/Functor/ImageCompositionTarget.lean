/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCompositionMap

/-! # Retain the original final proper-arrow transport after binary composition -/

@[expose] public section
namespace CategoryTheory
variable {A B C M N Z : Type*}
  [Category* A] [Category* B] [Category* C] [Category* M] [Category* N] [Category* Z]
  {K : A ⥤ B} {J : A ⥤ C} {L : B ⥤ C}
  {Q : B ⥤ M} {I : M ⥤ N} {R : C ⥤ N} {P : N ⥤ Z} {S S' : C ⥤ Z}

/-- The specified last proper comparison remains the actual postcomparison of the map. -/
theorem imageCompositionMap_change_target
    (σ : Q ⋙ I ⟶ L ⋙ R) (c : K ⋙ L ≅ J) (s : R ⋙ P ≅ S) (e : S ≅ S') :
    imageCompositionMap σ c (s ≪≫ e) =
      imageCompositionMap σ c s ≫ Functor.whiskerLeft J e.hom := by
  apply NatTrans.ext
  funext X
  simp only [imageCompositionMap, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.trans_hom, Category.assoc]

end CategoryTheory
