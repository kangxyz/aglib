/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.CoefficientSquare

/-! # Recovering whole square pasting from coefficient equations -/

@[expose] public section
namespace CategoryTheory

variable {A B C D E T : Type*}
  [Category A] [Category B] [Category C] [Category D] [Category E] [Category T]

/-- Test coefficient-morphism compatibility at identities to recover whole iso pasting. -/
lemma isoPastingOfCoefficientMorphisms
    (f : A ⥤ B) (h : C ⥤ D) (v₀ : A ⥤ C) (v₁ : B ⥤ D)
    (l : E ⥤ T) (p₀ : A ⥤ E) (p₁ : B ⥤ E) (q₀ : C ⥤ T) (q₁ : D ⥤ T)
    (tx : p₀ ≅ f ⋙ p₁) (ty : q₀ ≅ h ⋙ q₁)
    (s : v₀ ⋙ h ≅ f ⋙ v₁) (e₀ : v₀ ⋙ q₀ ≅ p₀ ⋙ l)
    (e₁ : v₁ ⋙ q₁ ≅ p₁ ⋙ l)
    (hc : ∀ {M : A} {N : B} (φ : f.obj M ⟶ N),
      ty.hom.app (v₀.obj M) ≫ q₁.map (s.hom.app M ≫ v₁.map φ) ≫ e₁.hom.app N =
        e₀.hom.app M ≫ l.map (tx.hom.app M ≫ p₁.map φ)) :
    Functor.isoWhiskerLeft v₀ ty ≪≫ (Functor.associator v₀ h q₁).symm ≪≫
        Functor.isoWhiskerRight s q₁ ≪≫ Functor.associator f v₁ q₁ ≪≫
        Functor.isoWhiskerLeft f e₁ ≪≫ (Functor.associator f p₁ l).symm =
      e₀ ≪≫ Functor.isoWhiskerRight tx l := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have ht := hc (𝟙 (f.obj M))
  have hs : s.hom.app M ≫ v₁.map (𝟙 (f.obj M)) = s.hom.app M :=
    (congrArg (fun z => s.hom.app M ≫ z) (v₁.map_id (f.obj M))).trans
      (Category.comp_id (s.hom.app M))
  have hx : tx.hom.app M ≫ p₁.map (𝟙 (f.obj M)) = tx.hom.app M :=
    (congrArg (fun z => tx.hom.app M ≫ z) (p₁.map_id (f.obj M))).trans
      (Category.comp_id (tx.hom.app M))
  rw [hs, hx] at ht
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_inv_app, Functor.associator_hom_app,
    Category.id_comp, Category.comp_id, Category.assoc] using ht

end CategoryTheory
