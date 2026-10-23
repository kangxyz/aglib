/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Evaluating whole square-pasting identities on a coefficient morphism -/

@[expose] public section
namespace CategoryTheory

variable {A B C D E T : Type*}
  [Category A] [Category B] [Category C] [Category D] [Category E] [Category T]

/-- A whole functor-square identity supplies the coefficient-morphism equation. -/
lemma coefficientSquareOfIsoPasting
    (f : A ⥤ B) (h : C ⥤ D) (v₀ : A ⥤ C) (v₁ : B ⥤ D)
    (l : E ⥤ T) (p₀ : A ⥤ E) (p₁ : B ⥤ E) (q₀ : C ⥤ T) (q₁ : D ⥤ T)
    (tx : p₀ ≅ f ⋙ p₁) (ty : q₀ ≅ h ⋙ q₁)
    (s : v₀ ⋙ h ≅ f ⋙ v₁) (e₀ : v₀ ⋙ q₀ ≅ p₀ ⋙ l)
    (e₁ : v₁ ⋙ q₁ ≅ p₁ ⋙ l)
    (hc : Functor.isoWhiskerLeft v₀ ty ≪≫ (Functor.associator v₀ h q₁).symm ≪≫
        Functor.isoWhiskerRight s q₁ ≪≫ Functor.associator f v₁ q₁ ≪≫
        Functor.isoWhiskerLeft f e₁ ≪≫ (Functor.associator f p₁ l).symm =
      e₀ ≪≫ Functor.isoWhiskerRight tx l)
    {M : A} {N : B} (φ : f.obj M ⟶ N) :
    ty.hom.app (v₀.obj M) ≫ q₁.map (s.hom.app M ≫ v₁.map φ) ≫ e₁.hom.app N =
      e₀.hom.app M ≫ l.map (tx.hom.app M ≫ p₁.map φ) := by
  have hv := congrArg (fun z => z.hom.app M) hc
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_inv_app, Functor.associator_hom_app,
    Category.id_comp, Category.comp_id] at hv
  have hn := e₁.hom.naturality φ
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]
  simpa only [Category.assoc] using congrArg (fun z => z ≫ l.map (p₁.map φ)) hv

end CategoryTheory
