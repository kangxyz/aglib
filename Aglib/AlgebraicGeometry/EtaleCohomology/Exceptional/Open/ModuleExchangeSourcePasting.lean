/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleSourceExchange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleExchangePasting

/-! # Original exchange under composition of its source -/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {V P U Y X : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ]
  (p : P ⟶ U) (q : P ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X)
  (h : p ≫ j = q ≫ f) (e : V ⟶ P)
  (he : (e ≫ p) ≫ j = (e ≫ q) ≫ f)

private theorem mapped_identity_chain {C D E : Type*}
    [Category C] [Category D] [Category E]
    {F H : C ⥤ D} {I : C ⥤ C} (L : D ⥤ E)
    (a : F ≅ I ⋙ H) (b : I ≅ 𝟭 C) (c : F ≅ H)
    (hc : a ≪≫ Functor.isoWhiskerRight b H ≪≫ Functor.leftUnitor H = c) (M : C) :
    L.map (a.hom.app M) ≫ L.map (H.map (b.hom.app M)) = L.map (c.hom.app M) := by
  have ht := congrArg (fun z : F ≅ H => z.hom.app M) hc
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at ht
  have hb := (congrArg (fun z => a.hom.app M ≫ z)
    (Category.comp_id (H.map (b.hom.app M)))).symm.trans ht
  exact (L.map_comp (a.hom.app M) (H.map (b.hom.app M))).symm.trans
    (congrArg L.map hb)

private theorem normalized_arrow_pasting {C : Type*} [Category C]
    {A B D E F G : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ F)
    (x : B ⟶ E) (y : E ⟶ F) (z : F ⟶ G) (t : A ⟶ D) (w : A ⟶ G)
    (hn : b ≫ c = x ≫ y) (hi : a ≫ b = t) (hv : a ≫ x ≫ y ≫ z = w) :
    t ≫ c ≫ z = w := by
  rw [← hi, Category.assoc, ← Category.assoc b, hn, Category.assoc]
  exact hv

private theorem indexed_map_transport {I : Type*} {C D E : Type*}
    [Category C] [Category D] [Category E] (F : I → C ⥤ D) (L : D ⥤ E)
    (H : C ⥤ E) (P : I → Prop) (α : ∀ k, P k → (F k ⋙ L ⟶ H))
    {a b : I} (h : a = b) (ha : P a) (hb : P b) (M : C) :
    L.map ((eqToIso (congrArg F h)).hom.app M) ≫ (α b hb).app M =
      (α a ha).app M := by
  subst b
  change L.map (𝟙 _) ≫ _ = _
  rw [L.map_id, Category.id_comp]

private theorem source_map_congr (f₀ f₁ : Y ⟶ X) (hf : f₀ = f₁)
    (p₀ : V ⟶ U) (q₀ : V ⟶ Y) (h₀ : p₀ ≫ j = q₀ ≫ f₀)
    (h₁ : p₀ ≫ j = q₀ ≫ f₁) (M : ModuleSheaf Y Λ) :
    (moduleInverseImage j Λ).map
        ((eqToIso (congrArg (fun k => moduleDirectImage k Λ) hf)).hom.app M) ≫
      (moduleBaseChangeMap Λ f₁ p₀ j q₀ h₁).app M =
    (moduleBaseChangeMap Λ f₀ p₀ j q₀ h₀).app M := by
  exact indexed_map_transport
    (fun k : Y ⟶ X => moduleDirectImage k Λ)
    (moduleInverseImage j Λ) (moduleInverseImage q₀ Λ ⋙ moduleDirectImage p₀ Λ)
    (fun k => p₀ ≫ j = q₀ ≫ k)
    (fun k hk => moduleBaseChangeMap Λ k p₀ j q₀ hk) hf h₀ h₁ M

private theorem source_pasting_expanded (M : ModuleSheaf Y Λ) :
    (moduleInverseImage j Λ).map ((moduleDirectImageCompIso Λ f (𝟙 Y)).hom.app M) ≫
      (moduleBaseChangeMap Λ f p j q h).app ((moduleDirectImage (𝟙 Y) Λ).obj M) ≫
      (moduleDirectImage p Λ).map
        ((moduleInverseImage q Λ).map ((moduleDirectImageIdIso Λ Y).hom.app M)) ≫
      (moduleDirectImage p Λ).map
        ((moduleInverseImageAdjunction e Λ).unit.app ((moduleInverseImage q Λ).obj M)) =
    (moduleBaseChangeMap Λ (𝟙 Y ≫ f) (e ≫ p) j (e ≫ q)
      (he.trans (by rw [Category.id_comp]))).app M ≫
      (moduleDirectImageCompIso Λ p e).hom.app ((moduleInverseImage (e ≫ q) Λ).obj M) ≫
      (moduleDirectImage p Λ).map ((moduleDirectImage e Λ).map
        ((moduleInverseImageCompIso Λ q e).hom.app M)) := by
  have hv := moduleBaseChangeMap_vComp Λ f (𝟙 Y) p e j q (e ≫ q) h
    (Category.comp_id (e ≫ q)).symm
    (he.trans (by rw [Category.id_comp])) M
  have hv' := congrArg (fun a => a ≫ (moduleDirectImage p Λ).map
    ((moduleDirectImage e Λ).map ((moduleInverseImageCompIso Λ q e).hom.app M))) hv
  rw [moduleBaseChangeMap_source Λ q e (e ≫ q) rfl M] at hv'
  simp only [moduleSourceInverseImageIso, eqToIso_refl, Iso.trans_inv,
    Iso.refl_inv, Category.comp_id,
    Functor.map_comp, Category.assoc] at hv'
  have hc : (moduleDirectImage p Λ).map ((moduleDirectImage e Λ).map
      ((moduleInverseImageCompIso Λ q e).inv.app M)) ≫
      (moduleDirectImage p Λ).map ((moduleDirectImage e Λ).map
        ((moduleInverseImageCompIso Λ q e).hom.app M)) = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app]
    exact (congrArg (moduleDirectImage p Λ).map ((moduleDirectImage e Λ).map_id _)).trans
      ((moduleDirectImage p Λ).map_id _)
  rw [hc] at hv'
  simp only [Functor.comp_obj] at hv'
  rw [Category.comp_id] at hv'
  exact hv'

private theorem source_pasting_normalized (M : ModuleSheaf Y Λ)
    (β : moduleDirectImage f Λ ⋙ moduleInverseImage j Λ ⟶
      moduleInverseImage q Λ ⋙ moduleDirectImage p Λ)
    (hv : (moduleInverseImage j Λ).map
        ((moduleDirectImageCompIso Λ f (𝟙 Y)).hom.app M) ≫
      β.app ((moduleDirectImage (𝟙 Y) Λ).obj M) ≫
      (moduleDirectImage p Λ).map
        ((moduleInverseImage q Λ).map ((moduleDirectImageIdIso Λ Y).hom.app M)) ≫
      (moduleDirectImage p Λ).map
        ((moduleInverseImageAdjunction e Λ).unit.app ((moduleInverseImage q Λ).obj M)) =
      (moduleBaseChangeMap Λ (𝟙 Y ≫ f) (e ≫ p) j (e ≫ q)
        (he.trans (by rw [Category.id_comp]))).app M ≫
      (moduleDirectImageCompIso Λ p e).hom.app ((moduleInverseImage (e ≫ q) Λ).obj M) ≫
      (moduleDirectImage p Λ).map ((moduleDirectImage e Λ).map
        ((moduleInverseImageCompIso Λ q e).hom.app M))) :
    (moduleInverseImage j Λ).map
      ((eqToIso (congrArg (fun k => moduleDirectImage k Λ)
        (Category.id_comp f))).hom.app M) ≫
      β.app M ≫
      (moduleDirectImage p Λ).map
        ((moduleInverseImageAdjunction e Λ).unit.app ((moduleInverseImage q Λ).obj M)) =
    (moduleBaseChangeMap Λ (𝟙 Y ≫ f) (e ≫ p) j (e ≫ q)
      (he.trans (by rw [Category.id_comp]))).app M ≫
      (moduleDirectImageCompIso Λ p e).hom.app ((moduleInverseImage (e ≫ q) Λ).obj M) ≫
      (moduleDirectImage p Λ).map ((moduleDirectImage e Λ).map
        ((moduleInverseImageCompIso Λ q e).hom.app M)) := by
  exact normalized_arrow_pasting _ _ _ _ _ _ _ _
    (β.naturality
      ((moduleDirectImageIdIso Λ Y).hom.app M))
    (mapped_identity_chain (moduleInverseImage j Λ)
      (moduleDirectImageCompIso Λ f (𝟙 Y)) (moduleDirectImageIdIso Λ Y) _
      (moduleDirectImageCompIso_comp_id Λ f) M)
    hv

/-- Source pasting retains the original source adjunction unit, before any invertibility. -/
@[reassoc]
theorem moduleBaseChangeMap_source_comp (M : ModuleSheaf Y Λ) :
    (moduleBaseChangeMap Λ f (e ≫ p) j (e ≫ q) he).app M ≫
      (moduleDirectImageCompIso Λ p e).hom.app ((moduleInverseImage (e ≫ q) Λ).obj M) ≫
      (moduleDirectImage p Λ).map ((moduleDirectImage e Λ).map
        ((moduleInverseImageCompIso Λ q e).hom.app M)) =
    (moduleBaseChangeMap Λ f p j q h).app M ≫
      (moduleDirectImage p Λ).map
        ((moduleInverseImageAdjunction e Λ).unit.app ((moduleInverseImage q Λ).obj M)) := by
  have hv' := source_pasting_normalized Λ p q j f e he M
    (moduleBaseChangeMap Λ f p j q h) (source_pasting_expanded Λ p q j f h e he M)
  rw [← source_map_congr Λ j (𝟙 Y ≫ f) f (Category.id_comp f)
    (e ≫ p) (e ≫ q) (he.trans (by rw [Category.id_comp])) he M] at hv'
  apply (cancel_epi ((moduleInverseImage j Λ).map
    ((eqToIso (congrArg (fun k => moduleDirectImage k Λ)
      (Category.id_comp f))).hom.app M))).1
  simpa only [Category.assoc] using hv'.symm

end AlgebraicGeometry.Scheme.EtaleCohomology
