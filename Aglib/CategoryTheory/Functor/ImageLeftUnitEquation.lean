/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageLeftUnitAssembly

/-! # A whole original-map boundary for the left-unit equation -/

@[expose] public section
namespace CategoryTheory
variable {A B B' C C' Z : Type*}
  [Category* A] [Category* B] [Category* B'] [Category* C] [Category* C'] [Category* Z]
  {V J : A ⥤ B} {J' : A ⥤ B'} {I : B ⥤ B}
  {L : B ⥤ C} {T' : A ⥤ C'} {R : B' ⥤ B} {S : C' ⥤ C}
  {P : C ⥤ Z} {P' : C' ⥤ Z}

/-- The source transition followed by the supplied map is the contracted total transition. -/
def ImageLeftUnitEquation (δT : V ⋙ L ⟶ T' ⋙ S) (e : S ⋙ P ≅ P')
    (α : J' ⋙ R ⋙ L ⋙ P ⟶ T' ⋙ P')
    (ε : J ⋙ I ≅ V) (τ : J ⋙ I ⟶ J' ⋙ R) : Prop :=
  Functor.whiskerRight τ (L ⋙ P) ≫ α =
    Functor.whiskerRight ε.hom (L ⋙ P) ≫
      imageComparison (L₁ := T') (L₂ := V ⋙ L) (R₁ := P') (R₂ := P) (F := S) δT e

/-- All three supplied input equations are proved from the original maps. -/
theorem imageLeftUnitEquation (δJ : J ⟶ J' ⋙ R) (δT : V ⋙ L ⟶ T' ⋙ S)
    (c : V ⋙ L ≅ J ⋙ L) (e : S ⋙ P ≅ P')
    (α : J' ⋙ R ⋙ L ⋙ P ⟶ T' ⋙ P')
    (ε : J ⋙ I ≅ V) (d : J ⋙ I ≅ J) (τ : J ⋙ I ⟶ J' ⋙ R)
    (hε : Functor.isoWhiskerRight ε L ≪≫ c = Functor.isoWhiskerRight d L)
    (hτ : τ = d.hom ≫ δJ)
    (hface : ImageUnitHorizontalEquation δJ δT c e α) :
    ImageLeftUnitEquation δT e α ε τ :=
  imageLeftUnitAssembly δJ δT c e α ε d τ hε hτ hface

end CategoryTheory
