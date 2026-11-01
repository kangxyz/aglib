/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageUnitHorizontal

/-! # Assemble the actual left-unit source contraction and image triangle -/

@[expose] public section
namespace CategoryTheory
variable {A B B' C C' Z : Type*}
  [Category* A] [Category* B] [Category* B'] [Category* C] [Category* C'] [Category* Z]
  {V J : A ⥤ B} {J' : A ⥤ B'} {I : B ⥤ B}
  {L : B ⥤ C} {T' : A ⥤ C'} {R : B' ⥤ B} {S : C' ⥤ C}
  {P : C ⥤ Z} {P' : C' ⥤ Z}

/-- Original source contraction and the proved image face give the actual left-unit map law. -/
theorem imageLeftUnitAssembly
    (δJ : J ⟶ J' ⋙ R) (δT : V ⋙ L ⟶ T' ⋙ S)
    (c : V ⋙ L ≅ J ⋙ L) (e : S ⋙ P ≅ P')
    (α : J' ⋙ R ⋙ L ⋙ P ⟶ T' ⋙ P')
    (ε : J ⋙ I ≅ V) (d : J ⋙ I ≅ J) (τ : J ⋙ I ⟶ J' ⋙ R)
    (hε : Functor.isoWhiskerRight ε L ≪≫ c = Functor.isoWhiskerRight d L)
    (hτ : τ = d.hom ≫ δJ)
    (hface : ImageUnitHorizontalEquation δJ δT c e α) :
    Functor.whiskerRight τ (L ⋙ P) ≫ α =
      Functor.whiskerRight ε.hom (L ⋙ P) ≫ imageComparison (L₁ := T') (L₂ := V ⋙ L)
        (R₁ := P') (R₂ := P) (F := S) δT e := by
  have hs := congrArg Iso.hom (congrArg (fun z => Functor.isoWhiskerRight z P) hε)
  simp only [Functor.isoWhiskerRight_trans, Iso.trans_hom,
    Functor.isoWhiskerRight_hom] at hs
  change Functor.whiskerRight ε.hom (L ⋙ P) ≫ Functor.whiskerRight c.hom P =
    Functor.whiskerRight d.hom (L ⋙ P) at hs
  have ht := congrArg (fun z => Functor.whiskerRight ε.hom (L ⋙ P) ≫ z) hface
  change Functor.whiskerRight ε.hom (L ⋙ P) ≫
      (Functor.whiskerRight c.hom P ≫ Functor.whiskerRight δJ (L ⋙ P) ≫ α) = _ at ht
  rw [← Category.assoc (Functor.whiskerRight ε.hom (L ⋙ P)), hs] at ht
  rw [hτ, Functor.whiskerRight_comp]
  simpa only [Category.assoc] using ht

end CategoryTheory
