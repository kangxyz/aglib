/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Normalize an original associativity equation by specified target comparisons -/

@[expose] public section
namespace CategoryTheory
variable {A B : Type*} [Category* A] [Category* B]
  {F : A ⥤ B} {Q : B ⥤ B} {M L R : A ⥤ B} {N : B ⥤ B}

/-- Retain all original intermediate functors. The three comparison squares,
not any implicit identification of models, normalize the actual equation. -/
theorem compositionAssociativity_normalize_identity
    (a : F ⋙ Q ≅ M) (b : M ⋙ Q ≅ L) (c : Q ⋙ Q ≅ N)
    (d : F ⋙ N ≅ R) (e : L ≅ R)
    (u : M ≅ F) (v : N ≅ Q) (l : L ≅ F) (t : R ≅ F)
    (hb : b ≪≫ l = Functor.isoWhiskerRight u Q ≪≫ a ≪≫ u)
    (hd : d ≪≫ t = Functor.isoWhiskerLeft F v ≪≫ a ≪≫ u)
    (he : e ≪≫ t = l)
    (ha : Functor.isoWhiskerRight a Q ≪≫ b ≪≫ e =
      Functor.associator F Q Q ≪≫ Functor.isoWhiskerLeft F c ≪≫ d) :
    Functor.isoWhiskerRight (a ≪≫ u) Q ≪≫ (a ≪≫ u) =
      Functor.associator F Q Q ≪≫ Functor.isoWhiskerLeft F (c ≪≫ v) ≪≫ (a ≪≫ u) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hk := congrArg (fun z => (z ≪≫ t).hom.app K) ha
  have hbK := congrArg (fun z => z.hom.app K) hb
  have hdK := congrArg (fun z => z.hom.app K) hd
  have heK := congrArg (fun z => z.hom.app K) he
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, Category.assoc] at hk hbK hdK heK ⊢
  rw [heK, hbK, hdK] at hk
  simpa only [Functor.map_comp, Category.assoc] using hk

end CategoryTheory
