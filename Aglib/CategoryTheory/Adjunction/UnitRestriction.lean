/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Restricting an exchange using an invertible unit

An exchange and a fully faithful unit induce an actual restriction comparison.
The component formula and its invertibility are proved before any application
to concrete sheaf or derived categories.
-/

@[expose] public noncomputable section

namespace CategoryTheory

namespace Functor

variable {A B C D T : Type*} [Category A] [Category B] [Category C]
  [Category D] [Category T]

/-- Restrict a right exchange along a fully faithful unit. -/
def restrictionOfUnit (I : T ⥤ A) (J : A ⥤ B) (Q' : B ⥤ A)
    (R : B ⥤ D) (Q : D ⥤ C) (R' : A ⥤ C)
    (β : R ⋙ Q ⟶ Q' ⋙ R') (η : 𝟭 A ≅ J ⋙ Q') :
    (I ⋙ J ⋙ R) ⋙ Q ⟶ I ⋙ R' :=
  (Functor.associator I (J ⋙ R) Q).hom ≫ Functor.whiskerLeft I
    ((Functor.associator J R Q).hom ≫ Functor.whiskerLeft J β ≫
      (Functor.associator J Q' R').inv ≫ Functor.whiskerRight η.inv R' ≫
      (Functor.leftUnitor R').hom)

/-- The restriction map retains the original exchange component. -/
theorem restrictionOfUnit_app (I : T ⥤ A) (J : A ⥤ B) (Q' : B ⥤ A)
    (R : B ⥤ D) (Q : D ⥤ C) (R' : A ⥤ C)
    (β : R ⋙ Q ⟶ Q' ⋙ R') (η : 𝟭 A ≅ J ⋙ Q') (K : T) :
    (restrictionOfUnit I J Q' R Q R' β η).app K =
      β.app (J.obj (I.obj K)) ≫ R'.map (η.inv.app (I.obj K)) := by
  simp [restrictionOfUnit]

/-- Componentwise exchange invertibility makes its unit restriction invertible. -/
theorem restrictionOfUnit_isIso (I : T ⥤ A) (J : A ⥤ B) (Q' : B ⥤ A)
    (R : B ⥤ D) (Q : D ⥤ C) (R' : A ⥤ C)
    (β : R ⋙ Q ⟶ Q' ⋙ R') (η : 𝟭 A ≅ J ⋙ Q')
    (h : ∀ K : T, IsIso (β.app (J.obj (I.obj K)))) :
    IsIso (restrictionOfUnit I J Q' R Q R' β η) := by
  have h' (K : T) : IsIso ((restrictionOfUnit I J Q' R Q R' β η).app K) := by
    rw [restrictionOfUnit_app]
    let := h K
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- Whole-transformation form, keeping component evaluation inside the abstract layer. -/
theorem restrictionOfUnit_isIso_of_whisker (I : T ⥤ A) (J : A ⥤ B) (Q' : B ⥤ A)
    (R : B ⥤ D) (Q : D ⥤ C) (R' : A ⥤ C)
    (β : R ⋙ Q ⟶ Q' ⋙ R') (η : 𝟭 A ≅ J ⋙ Q')
    (h : IsIso (whiskerLeft (I ⋙ J) β)) :
    IsIso (restrictionOfUnit I J Q' R Q R' β η) := by
  apply restrictionOfUnit_isIso
  intro K
  exact inferInstanceAs (IsIso ((whiskerLeft (I ⋙ J) β).app K))

/-- Globally invertible exchange gives an invertible unit restriction. -/
theorem restrictionOfUnit_isIso_of_isIso (I : T ⥤ A) (J : A ⥤ B) (Q' : B ⥤ A)
    (R : B ⥤ D) (Q : D ⥤ C) (R' : A ⥤ C)
    (β : R ⋙ Q ⟶ Q' ⋙ R') (η : 𝟭 A ≅ J ⋙ Q') [IsIso β] :
    IsIso (restrictionOfUnit I J Q' R Q R' β η) :=
  restrictionOfUnit_isIso_of_whisker I J Q' R Q R' β η inferInstance


end Functor

end CategoryTheory

