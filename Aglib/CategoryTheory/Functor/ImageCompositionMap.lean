/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCompositionAssembly

/-! # The natural map built from the specified interchange and original compositors -/

@[expose] public section
namespace CategoryTheory
variable {A B C M N Z : Type*}
  [Category* A] [Category* B] [Category* C] [Category* M] [Category* N] [Category* Z]
  {K : A ⥤ B} {J : A ⥤ C} {L : B ⥤ C}
  {Q : B ⥤ M} {I : M ⥤ N} {R : C ⥤ N} {P : N ⥤ Z} {S : C ⥤ Z}

/-- This map uses the supplied interchange and the supplied open and proper compositors. -/
def imageCompositionMap (σ : Q ⋙ I ⟶ L ⋙ R) (c : K ⋙ L ≅ J) (s : R ⋙ P ≅ S) :
    K ⋙ Q ⋙ I ⋙ P ⟶ J ⋙ S :=
  Functor.whiskerRight (Functor.whiskerLeft K σ) P ≫
    Functor.whiskerRight c.hom (R ⋙ P) ≫ Functor.whiskerLeft J s.hom

/-- Its component formula records exactly those specified original maps. -/
theorem imageCompositionMap_formula (σ : Q ⋙ I ⟶ L ⋙ R)
    (c : K ⋙ L ≅ J) (s : R ⋙ P ≅ S) :
    ImageCompositionFormula σ c s (imageCompositionMap σ c s) := by
  intro X
  rfl

/-- A supplied map with the same original formula is the same natural transformation. -/
theorem imageCompositionMap_eq (σ : Q ⋙ I ⟶ L ⋙ R)
    (c : K ⋙ L ≅ J) (s : R ⋙ P ≅ S)
    (α : K ⋙ Q ⋙ I ⋙ P ⟶ J ⋙ S) (h : ImageCompositionFormula σ c s α) :
    imageCompositionMap σ c s = α := by
  apply NatTrans.ext
  funext X
  exact (h X).symm

end CategoryTheory
