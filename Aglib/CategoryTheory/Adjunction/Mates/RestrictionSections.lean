/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Original exchange sections through an actual restriction factorization

The original exchange and both actual evaluation maps remain explicit aliases.
Their proven defining equations are substituted while the functors are still
abstract, so specialization retains the original map heads.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

/-- An actual restriction factorization and the original evaluation path
identify sections of the original exchange without replacing its map. -/
theorem exchange_sections_of_restriction_factorization
    {A B C D E : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D] [Category* E]
    (R₁ : B ⥤ A) (R₂ : D ⥤ C) (G G₀ : A ⥤ C) (H H₀ : B ⥤ D)
    (ΓC : C ⥤ E) (ΓD : D ⥤ E)
    (s : G ≅ G₀) (t : H ≅ H₀) (δ : R₁ ⋙ G₀ ≅ H₀ ⋙ R₂)
    (e : R₂ ⋙ ΓC ≅ ΓD) (α : R₁ ⋙ G ⟶ H ⋙ R₂)
    (hα : α = (Functor.isoWhiskerLeft R₁ s ≪≫ δ ≪≫
      Functor.isoWhiskerRight t.symm R₂).hom)
    (M : B) (Z : E) (p : ΓD.obj (H₀.obj M) ⟶ Z)
    (q : ΓC.obj (G₀.obj (R₁.obj M)) ⟶ Z)
    (a : ΓD.obj (H.obj M) ⟶ Z) (a₀ : ΓC.obj (G.obj (R₁.obj M)) ⟶ Z)
    (ha : a = ΓD.map (t.hom.app M) ≫ p)
    (ha₀ : a₀ = ΓC.map (s.hom.app (R₁.obj M)) ≫ q)
    (hp : ΓC.map (δ.hom.app M) ≫ e.hom.app (H₀.obj M) ≫ p = q) :
    ΓC.map (α.app M) ≫ e.hom.app (H.obj M) ≫ a = a₀ := by
  subst α
  subst a
  subst a₀
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, ΓC.map_comp, Category.assoc]
  have hn := e.hom.naturality (t.inv.app M)
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  have hi : ΓD.map (t.inv.app M) ≫ ΓD.map (t.hom.app M) = 𝟙 _ := by
    rw [← ΓD.map_comp, Iso.inv_hom_id_app, ΓD.map_id]
  rw [reassoc_of% hi, hp]

end CategoryTheory
