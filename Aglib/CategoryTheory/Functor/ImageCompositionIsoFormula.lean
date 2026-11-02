/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCompositionAssembly

/-! # The whole formula of a specified original image-composition isomorphism -/

@[expose] public section

namespace CategoryTheory

variable {A B C M N Z : Type*}
  [Category* A] [Category* B] [Category* C] [Category* M] [Category* N] [Category* Z]
  {K : A ⥤ B} {J : A ⥤ C} {L : B ⥤ C}
  {Q : B ⥤ M} {I : M ⥤ N} {R : C ⥤ N} {P : N ⥤ Z} {S : C ⥤ Z}

/-- Preserve the original whole interchange and the actual assembled isomorphism
before evaluating its components. -/
theorem imageCompositionFormula_of_originalIso
    (e : ((𝟭 B) ⋙ Q) ⋙ I ≅ (𝟭 B) ⋙ L ⋙ R)
    (σ : Q ⋙ I ⟶ L ⋙ R) (c : K ⋙ L ≅ J) (s : R ⋙ P ≅ S)
    (α : K ⋙ Q ⋙ I ⋙ P ≅ J ⋙ S)
    (he : e.hom = (Functor.associator (𝟭 B) Q I).hom ≫
      Functor.whiskerLeft (𝟭 B) σ)
    (hα : α = Functor.isoWhiskerRight (Functor.isoWhiskerLeft K e) P ≪≫
      Functor.isoWhiskerRight c (R ⋙ P) ≪≫ Functor.isoWhiskerLeft J s) :
    ImageCompositionFormula σ c s α.hom := by
  subst α
  intro X
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map, Functor.comp_obj, he, Functor.associator_hom_app,
    Functor.id_obj, Category.id_comp]

end CategoryTheory
