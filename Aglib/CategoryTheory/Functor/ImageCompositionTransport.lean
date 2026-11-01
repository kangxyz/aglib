/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCompositionMap

/-! # Transport original binary image maps along specified natural comparisons -/

@[expose] public section
namespace CategoryTheory
variable {A B C M N Z : Type*}
  [Category* A] [Category* B] [Category* C] [Category* M] [Category* N] [Category* Z]
  {K : A ⥤ B} {J J' : A ⥤ C} {L : B ⥤ C}
  {Q : B ⥤ M} {I I' : M ⥤ N} {R : C ⥤ N} {P : N ⥤ Z} {S : C ⥤ Z}

/-- Changing only the output open compositor retains its actual postcomparison. -/
theorem imageCompositionMap_change_output
    (σ : Q ⋙ I ⟶ L ⋙ R) (c : K ⋙ L ≅ J) (e : J ≅ J') (s : R ⋙ P ≅ S) :
    imageCompositionMap σ (c ≪≫ e) s =
      imageCompositionMap σ c s ≫ Functor.whiskerRight e.hom S := by
  apply NatTrans.ext
  funext X
  have hn := s.hom.naturality (e.hom.app X)
  change P.map (R.map (e.hom.app X)) ≫ s.hom.app (J'.obj X) =
    s.hom.app (J.obj X) ≫ S.map (e.hom.app X) at hn
  simp only [imageCompositionMap, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.trans_hom, Functor.comp_map, Functor.map_comp,
    Category.assoc]
  rw [hn]

/-- An actual source-open comparison is precomposed, not replaced by an arbitrary isomorphism. -/
theorem imageCompositionMap_change_input
    (σ : Q ⋙ I ⟶ L ⋙ R) (σ' : Q ⋙ I' ⟶ L ⋙ R)
    (e : I ⟶ I') (h : σ = Functor.whiskerLeft Q e ≫ σ')
    (c : K ⋙ L ≅ J) (s : R ⋙ P ≅ S) :
    imageCompositionMap σ c s =
      Functor.whiskerRight (Functor.whiskerLeft (K ⋙ Q) e) P ≫
        imageCompositionMap σ' c s := by
  subst σ
  apply NatTrans.ext
  funext X
  simp only [imageCompositionMap, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.map_comp, Functor.comp_obj, Category.assoc]

end CategoryTheory
