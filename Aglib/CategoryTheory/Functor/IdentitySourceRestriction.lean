/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Whole source restriction of the original identity-expansion equation -/

@[expose] public section
namespace CategoryTheory
variable {A D B : Type*} [Category* A] [Category* D] [Category* B]
  {J I : A ⥤ A} {L : A ⥤ B}

/-- Source restriction retains the actual contraction, including its original unitor. -/
theorem identitySourceExpansion_whiskerLeft (V : D ⥤ A)
    (ε : J ⋙ I ≅ 𝟭 A) (d : J ⋙ I ≅ J) (c : L ≅ J ⋙ L)
    (h : Functor.isoWhiskerRight ε L ≪≫ Functor.leftUnitor L ≪≫ c =
      Functor.isoWhiskerRight d L) :
    Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft V ε ≪≫ Functor.rightUnitor V) L ≪≫
      Functor.isoWhiskerLeft V c =
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft V d) L := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hk := congrArg (fun z => z.hom.app (V.obj K)) h
  change L.map (ε.hom.app (V.obj K)) ≫ 𝟙 (L.obj (V.obj K)) ≫
      c.hom.app (V.obj K) = L.map (d.hom.app (V.obj K)) at hk
  have hi : 𝟙 (L.obj (V.obj K)) ≫ c.hom.app (V.obj K) = c.hom.app (V.obj K) :=
    Category.id_comp _
  rw [hi] at hk
  change L.map (ε.hom.app (V.obj K) ≫ 𝟙 (V.obj K)) ≫ c.hom.app (V.obj K) = _
  have he : ε.hom.app (V.obj K) ≫ 𝟙 (V.obj K) = ε.hom.app (V.obj K) :=
    Category.comp_id _
  rw [he]
  exact hk

end CategoryTheory
