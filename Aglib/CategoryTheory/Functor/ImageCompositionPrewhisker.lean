/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCompositionMap

/-! # Restrict the actual binary map without changing any original factor -/

@[expose] public section
namespace CategoryTheory
variable {A A' B C M N Z : Type*}
  [Category* A] [Category* A'] [Category* B] [Category* C]
  [Category* M] [Category* N] [Category* Z]
  {K : A ⥤ B} {J : A ⥤ C} {L : B ⥤ C}
  {Q : B ⥤ M} {I : M ⥤ N} {R : C ⥤ N} {P : N ⥤ Z} {S : C ⥤ Z}

/-- Restriction is literally the same specified original map on restricted objects. -/
theorem imageCompositionMap_whiskerLeft (V : A' ⥤ A)
    (σ : Q ⋙ I ⟶ L ⋙ R) (c : K ⋙ L ≅ J) (s : R ⋙ P ≅ S) :
    imageCompositionMap (K := V ⋙ K) (J := V ⋙ J) σ
        (Functor.isoWhiskerLeft V c) s =
      Functor.whiskerLeft V (imageCompositionMap σ c s) := by
  apply NatTrans.ext
  funext X
  rfl

end CategoryTheory
