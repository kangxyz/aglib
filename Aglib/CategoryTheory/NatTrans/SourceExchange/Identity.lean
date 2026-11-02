/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.NormalizedIdentity
public import Mathlib.CategoryTheory.Whiskering

/-! # Original exchange coherence over independently sized categories -/

@[expose] public noncomputable section

namespace CategoryTheory

universe uA uB uC uA' vA vB vC vA'

theorem identitySource_compare
    {A : Type uA} {B : Type uB} {C : Type uC} [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    {F G : A ⥤ B} {H I : C ⥤ B} {V : A ⥤ C}
    (c : F ≅ G) (d : H ≅ I) (s t : G ≅ V ⋙ I) (p q : F ≅ V ⋙ H)
    (hs : c ≪≫ s = p ≪≫ Functor.isoWhiskerLeft V d)
    (ht : c ≪≫ t = q ≪≫ Functor.isoWhiskerLeft V d) (h : s = t) : p = q := by
  have hh := hs.symm.trans ((congrArg (fun z => c ≪≫ z) h).trans ht)
  exact Iso.ext ((cancel_mono (Functor.isoWhiskerLeft V d).hom).mp (congrArg Iso.hom hh))

theorem identitySource_post_self
    {A : Type uA} {B : Type uB} {C : Type uC} [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    {F : A ⥤ C} {V : A ⥤ B} {G : B ⥤ C}
    (s : F ≅ V ⋙ G) (c : G ≅ G) (hc : c = Iso.refl G) :
    s ≪≫ Functor.isoWhiskerLeft V c = s := by
  subst c
  simp only [Functor.isoWhiskerLeft_refl, Iso.trans_refl]

theorem normalizedIdentityIso_of_equation
    {A : Type uA} {B : Type uB} {A' : Type uA'} [Category.{vA} A] [Category.{vB} B]
    [Category.{vA'} A']
    {F : A ⥤ B} {I : B ⥤ B} {V : A ⥤ A'} {D N : A' ⥤ B}
    (β : F ⋙ I ≅ V ⋙ N) (i : I ≅ 𝟭 B) (s : F ≅ V ⋙ D)
    (τ : D ⟶ N) (hτ : IsIso τ) (Ψ : F ≅ V ⋙ N)
    (hΨ : Ψ = s ≪≫ Functor.isoWhiskerLeft V (@asIso _ _ _ _ τ hτ))
    (h : NormalizedIdentityBaseChangeEquation β.hom i s τ) :
    β = Functor.isoWhiskerLeft F i ≪≫ Functor.rightUnitor F ≪≫ Ψ := by
  subst Ψ
  apply Iso.ext
  exact h

theorem inverse_compositor_normalization
    {C : Type uC} [Category.{vC} C] {A B D : C}
    (c : A ≅ B) (d : B ≅ D) (t : A ≅ D) (h : c ≪≫ d = t) : c.symm ≪≫ t = d := by
  rw [← h, ← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

end CategoryTheory
