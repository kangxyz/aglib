/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.CompositionChoice

/-! # Transfer binary composition associativity through specified comparisons

The comparison squares retain the supplied binary maps. Associativity is
transported from those maps, not installed as a new structure or hypothesis on
the chosen compositor in downstream applications.
-/

@[expose] public section
namespace CategoryTheory
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]

@[simp]
lemma compositionPairIso_refl_right {F G : A ⥤ B} (e : F ≅ G) (H : B ⥤ C) :
    compositionPairIso e (Iso.refl H) = Functor.isoWhiskerRight e H := by
  apply Iso.ext
  ext X
  simp [compositionPairIso]

@[simp]
lemma compositionPairIso_refl_left (F : A ⥤ B) {G H : B ⥤ C} (e : G ≅ H) :
    compositionPairIso (Iso.refl F) e = Functor.isoWhiskerLeft F e := by
  apply Iso.ext
  ext X
  simp [compositionPairIso]

/-- Horizontal composition carries two commuting comparison squares to one. -/
lemma compositionPairIso_square
    {F₀ F₁ F₂ F₃ : A ⥤ B} {G₀ G₁ G₂ G₃ : B ⥤ C}
    (p : F₀ ≅ F₁) (q : G₀ ≅ G₁)
    (a : F₁ ≅ F₂) (b : G₁ ≅ G₂)
    (c : F₀ ≅ F₃) (d : G₀ ≅ G₃)
    (r : F₃ ≅ F₂) (s : G₃ ≅ G₂)
    (hf : p ≪≫ a = c ≪≫ r) (hg : q ≪≫ b = d ≪≫ s) :
    compositionPairIso p q ≪≫ compositionPairIso a b =
      compositionPairIso c d ≪≫ compositionPairIso r s := by
  simp only [compositionPairIso_trans, hf, hg]

/-- The ordinary functor associator commutes with the three model comparisons. -/
lemma compositionPairIso_associator
    {F F' : A ⥤ B} {G G' : B ⥤ C} {H H' : C ⥤ D}
    (p : F ≅ F') (q : G ≅ G') (r : H ≅ H') :
    compositionPairIso (compositionPairIso p q) r ≪≫ Functor.associator F' G' H' =
      Functor.associator F G H ≪≫ compositionPairIso p (compositionPairIso q r) := by
  apply Iso.ext
  ext X
  simp [compositionPairIso]

/-- Associativity descends through four specified binary comparison squares and
one specified total-target comparison. All chosen and model functors are independent. -/
theorem compositionAssociativity_transfer
    {F F' : A ⥤ B} {G G' : B ⥤ C} {H H' : C ⥤ D}
    {FG FG' : A ⥤ C} {GH GH' : B ⥤ D}
    {L L' R R' : A ⥤ D}
    (p : F ≅ F') (q : G ≅ G') (r : H ≅ H')
    (pq : FG ≅ FG') (qr : GH ≅ GH') (l : L ≅ L') (t : R ≅ R')
    (a : F ⋙ G ≅ FG) (b : FG ⋙ H ≅ L)
    (c : G ⋙ H ≅ GH) (d : F ⋙ GH ≅ R) (e : L ≅ R)
    (a' : F' ⋙ G' ≅ FG') (b' : FG' ⋙ H' ≅ L')
    (c' : G' ⋙ H' ≅ GH') (d' : F' ⋙ GH' ≅ R') (e' : L' ≅ R')
    (ha : compositionPairIso p q ≪≫ a' = a ≪≫ pq)
    (hb : compositionPairIso pq r ≪≫ b' = b ≪≫ l)
    (hc : compositionPairIso q r ≪≫ c' = c ≪≫ qr)
    (hd : compositionPairIso p qr ≪≫ d' = d ≪≫ t)
    (he : l ≪≫ e' = e ≪≫ t)
    (hassoc : Functor.isoWhiskerRight a' H' ≪≫ b' ≪≫ e' =
      Functor.associator F' G' H' ≪≫ Functor.isoWhiskerLeft F' c' ≪≫ d') :
    Functor.isoWhiskerRight a H ≪≫ b ≪≫ e =
      Functor.associator F G H ≪≫ Functor.isoWhiskerLeft F c ≪≫ d := by
  have hleft := compositionPairIso_square
    (compositionPairIso p q) r a' (Iso.refl H') a (Iso.refl H) pq r ha (by simp)
  have hright := compositionPairIso_square
    p (compositionPairIso q r) (Iso.refl F') c' (Iso.refl F) c p qr (by simp) hc
  simp only [compositionPairIso_refl_right, compositionPairIso_refl_left] at hleft hright
  have hroute :
      compositionPairIso (compositionPairIso p q) r ≪≫
          (Functor.isoWhiskerRight a' H' ≪≫ b' ≪≫ e') =
        (Functor.isoWhiskerRight a H ≪≫ b ≪≫ e) ≪≫ t := by
    rw [← Iso.trans_assoc, ← Iso.trans_assoc, hleft]
    simp only [Iso.trans_assoc]
    rw [← Iso.trans_assoc (compositionPairIso pq r), hb]
    simp only [Iso.trans_assoc]
    rw [he]
  have hroute' :
      compositionPairIso (compositionPairIso p q) r ≪≫
          (Functor.associator F' G' H' ≪≫ Functor.isoWhiskerLeft F' c' ≪≫ d') =
        (Functor.associator F G H ≪≫ Functor.isoWhiskerLeft F c ≪≫ d) ≪≫ t := by
    rw [← Iso.trans_assoc, ← Iso.trans_assoc, compositionPairIso_associator]
    simp only [Iso.trans_assoc]
    rw [← Iso.trans_assoc (compositionPairIso p (compositionPairIso q r)), hright]
    simp only [Iso.trans_assoc]
    rw [hd]
  apply Iso.ext
  have hh := congrArg Iso.hom (hroute.symm.trans ((congrArg
    (fun z => compositionPairIso (compositionPairIso p q) r ≪≫ z) hassoc).trans hroute'))
  exact (cancel_mono t.hom).mp hh

end CategoryTheory
