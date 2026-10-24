/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleCartesianExchangeMate
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleIdentityCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleExchangePasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleSourceExchange

/-! # Coherence of the original identity-source Cartesian exchange -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

private theorem adjusted_exchange_app
    {C D : Type*} [Category* C] [Category* D]
    {F L : C ⥤ D} {I : D ⥤ D} (a : F ≅ L ⋙ I) (d : I ≅ 𝟭 D) (M : C) :
    (a ≪≫ Functor.isoWhiskerLeft L d ≪≫ Functor.rightUnitor L).hom.app M =
      a.hom.app M ≫ d.hom.app (L.obj M) := by
  simp

private theorem normalized_left_identity_app
    {C D : Type*} [Category* C] [Category* D]
    {I : C ⥤ C} (d : I ≅ 𝟭 C) (L : C ⥤ D) (M : C) :
    (Functor.isoWhiskerRight d L ≪≫ Functor.leftUnitor L).hom.app M =
      L.map (d.hom.app M) := by
  simp

private theorem adjusted_composition_app
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {K : A ⥤ B} {F : B ⥤ C} {T : A ⥤ C} {L : C ⥤ D}
    {J : B ⥤ D} {I : A ⥤ D} (c : T ≅ K ⋙ F) (a : F ⋙ L ≅ J)
    (b : K ⋙ J ≅ I) (M : A) :
    (Functor.isoWhiskerRight c L ≪≫ Functor.associator K F L ≪≫
      Functor.isoWhiskerLeft K a ≪≫ b).hom.app M =
    L.map (c.hom.app M) ≫ a.hom.app (K.obj M) ≫ b.hom.app M := by
  simp

private theorem normalized_right_identity_app
    {C D : Type*} [Category* C] [Category* D]
    {F L : C ⥤ D} {I : D ⥤ D} (c : F ≅ L ⋙ I) (d : I ≅ 𝟭 D)
    (t : F ≅ L)
    (h : c ≪≫ Functor.isoWhiskerLeft L d ≪≫ Functor.rightUnitor L = t) (M : C) :
    c.hom.app M ≫ d.hom.app (L.obj M) = t.hom.app M := by
  rw [← adjusted_exchange_app, h]

private theorem normalized_source_inverse_app
    {C D : Type*} [Category* C] [Category* D]
    {F L : C ⥤ D} {I : D ⥤ D} (c : F ≅ L ⋙ I) (d : I ≅ 𝟭 D)
    (t : F ≅ L)
    (h : c ≪≫ Functor.isoWhiskerLeft L d ≪≫ Functor.rightUnitor L = t) (M : C) :
    (t.symm ≪≫ c).inv.app M = d.hom.app (L.obj M) := by
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]
  apply (cancel_epi (c.hom.app M)).1
  rw [Iso.hom_inv_id_app_assoc]
  exact (normalized_right_identity_app c d t h M).symm

private theorem indexed_target_transport
    {J C D E : Type*} [Category* C] [Category* D] [Category* E]
    (R : J → D ⥤ E) (F : C ⥤ E) (L : C ⥤ D) (P : J → Prop)
    (α : ∀ j, P j → (F ⟶ L ⋙ R j)) {a b : J} (h : a = b)
    (ha : P a) (hb : P b) (M : C) :
    (α a ha).app M ≫ (eqToIso (congrArg R h)).hom.app (L.obj M) =
      (α b hb).app M := by
  subst b
  simp

private theorem adjusted_pasting
    {C : Type*} [Category* C] {A B C₁ D E F G H : C}
    (a : A ⟶ B) (b : B ⟶ C₁) (c : C₁ ⟶ D) (d : D ⟶ E) (e : E ⟶ F)
    (r : C₁ ⟶ G) (s : G ⟶ E) (t : A ⟶ H) (u : H ⟶ D)
    (v : H ⟶ E) (w : A ⟶ E)
    (hn : c ≫ d = r ≫ s) (hp : a ≫ b ≫ c = t ≫ u)
    (hd : u ≫ d = v) (ht : t ≫ v = w) :
    w ≫ e = a ≫ b ≫ r ≫ s ≫ e := by
  symm
  rw [← reassoc_of% hn, reassoc_of% hp, reassoc_of% hd, reassoc_of% ht]

private theorem remove_unit_tail
    {C : Type*} [Category* C] {A B D E : C}
    (a : A ⟶ B) (u : B ⟶ D) (v : D ⟶ E) (d : E ⟶ B)
    (h : u ≫ v ≫ d = 𝟙 B) : (a ≫ u ≫ v) ≫ d = a := by
  simp only [Category.assoc, h, Category.comp_id]

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

/-- The original Cartesian exchange, with its identity direct image removed. -/
def moduleRefinementExchangeIso {U Y X : Scheme.{u}}
    (i : U ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X) [Etale j]
    (h : IsPullback (𝟙 U) i j f) (Λ : Type (u + 1)) [Ring Λ] :
    moduleDirectImage f Λ ⋙ moduleInverseImage j Λ ≅ moduleInverseImage i Λ :=
  moduleCartesianExchangeIso (𝟙 U) i j f h Λ ≪≫
    Functor.isoWhiskerLeft (moduleInverseImage i Λ) (moduleDirectImageIdIso Λ U) ≪≫
    Functor.rightUnitor (moduleInverseImage i Λ)

/-- Evaluation retains the original native mate and direct-image identity. -/
theorem moduleRefinementExchangeIso_hom_app {U Y X : Scheme.{u}}
    (i : U ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X) [Etale j]
    (h : IsPullback (𝟙 U) i j f) (Λ : Type (u + 1)) [Ring Λ]
    (M : ModuleSheaf Y Λ) :
    (moduleRefinementExchangeIso i j f h Λ).hom.app M =
      (moduleBaseChangeMap Λ f (𝟙 U) j i h.w).app M ≫
        (moduleDirectImageIdIso Λ U).hom.app ((moduleInverseImage i Λ).obj M) := by
  change (moduleCartesianExchangeIso (𝟙 U) i j f h Λ ≪≫
    Functor.isoWhiskerLeft (moduleInverseImage i Λ) (moduleDirectImageIdIso Λ U) ≪≫
    Functor.rightUnitor (moduleInverseImage i Λ)).hom.app M = _
  rw [adjusted_exchange_app, moduleCartesianExchangeIso_hom]

/-- Original vertical mate pasting after cancelling both identity direct images. -/
theorem moduleBaseChangeMap_identity_source_comp {U Z Y X : Scheme.{u}}
    (i : U ⟶ Z) (j : U ⟶ Y) (l : U ⟶ X) (f : Y ⟶ X) (k : Z ⟶ Y)
    (hf : (𝟙 U) ≫ l = j ≫ f) (hk : (𝟙 U) ≫ j = i ≫ k)
    (ht : (𝟙 U) ≫ l = i ≫ (k ≫ f)) (Λ : Type (u + 1)) [Ring Λ]
    (M : ModuleSheaf Z Λ) :
    (moduleBaseChangeMap Λ (k ≫ f) (𝟙 U) l i ht).app M ≫
        (moduleDirectImageIdIso Λ U).hom.app ((moduleInverseImage i Λ).obj M) =
      (moduleInverseImage l Λ).map ((moduleDirectImageCompIso Λ f k).hom.app M) ≫
        (moduleBaseChangeMap Λ f (𝟙 U) l j hf).app ((moduleDirectImage k Λ).obj M) ≫
        (moduleDirectImageIdIso Λ U).hom.app
          ((moduleInverseImage j Λ).obj ((moduleDirectImage k Λ).obj M)) ≫
        (moduleBaseChangeMap Λ k (𝟙 U) j i hk).app M ≫
        (moduleDirectImageIdIso Λ U).hom.app ((moduleInverseImage i Λ).obj M) := by
  let et : ((𝟙 U) ≫ (𝟙 U)) ≫ l = i ≫ (k ≫ f) :=
    (congrArg (fun a : U ⟶ U => a ≫ l) (Category.id_comp (𝟙 U))).trans ht
  have hp := moduleBaseChangeMap_vComp Λ f k (𝟙 U) (𝟙 U) l j i hf hk et M
  have hn := (moduleDirectImageIdIso Λ U).hom.naturality
    ((moduleBaseChangeMap Λ k (𝟙 U) j i hk).app M)
  have hd := normalized_right_identity_app
    (moduleDirectImageCompIso Λ (𝟙 U) (𝟙 U)) (moduleDirectImageIdIso Λ U)
    (eqToIso (congrArg (fun a : U ⟶ U => moduleDirectImage a Λ)
      (Category.comp_id (𝟙 U))))
    (moduleDirectImageCompIso_id_comp Λ (𝟙 U)) ((moduleInverseImage i Λ).obj M)
  have ht' := indexed_target_transport
    (fun a : U ⟶ U => moduleDirectImage a Λ)
    (moduleDirectImage (k ≫ f) Λ ⋙ moduleInverseImage l Λ) (moduleInverseImage i Λ)
    (fun a : U ⟶ U => a ≫ l = i ≫ (k ≫ f))
    (fun a ha => moduleBaseChangeMap Λ (k ≫ f) a l i ha)
    (Category.comp_id (𝟙 U)) et ht M
  exact adjusted_pasting _ _ _ _ _ _ _ _ _ _ _ hn hp hd ht'

/-- The original identity square mate becomes the inverse-image of the direct identity. -/
theorem moduleBaseChangeMap_identity_source_id {U X : Scheme.{u}}
    (i : U ⟶ X) (h : (𝟙 U) ≫ i = i ≫ (𝟙 X))
    (Λ : Type (u + 1)) [Ring Λ] (M : ModuleSheaf X Λ) :
    (moduleBaseChangeMap Λ (𝟙 X) (𝟙 U) i i h).app M ≫
        (moduleDirectImageIdIso Λ U).hom.app ((moduleInverseImage i Λ).obj M) =
      (moduleInverseImage i Λ).map ((moduleDirectImageIdIso Λ X).hom.app M) := by
  have hs := normalized_source_inverse_app (moduleInverseImageCompIso Λ i (𝟙 U))
    (moduleInverseImageIdIso Λ U)
    (eqToIso (congrArg (fun a : U ⟶ X => moduleInverseImage a Λ) (Category.id_comp i)))
    (moduleInverseImageCompIso_comp_id Λ i) M
  change (moduleSourceInverseImageIso Λ i (𝟙 U) i (Category.id_comp i)).inv.app M =
    (moduleInverseImageIdIso Λ U).hom.app ((moduleInverseImage i Λ).obj M) at hs
  rw [moduleBaseChangeMap_source Λ i (𝟙 U) i (Category.id_comp i) M, hs]
  exact remove_unit_tail _ _ _ _ (moduleInverseImageIdIso_unit Λ U _)

/-- The adjusted exchange for an identity refinement is the native direct identity. -/
theorem moduleRefinementExchangeIso_id {U X : Scheme.{u}}
    (i : U ⟶ X) [Etale i] (h : IsPullback (𝟙 U) i i (𝟙 X))
    (Λ : Type (u + 1)) [Ring Λ] :
    moduleRefinementExchangeIso i i (𝟙 X) h Λ =
      Functor.isoWhiskerRight (moduleDirectImageIdIso Λ X) (moduleInverseImage i Λ) ≪≫
        Functor.leftUnitor (moduleInverseImage i Λ) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  rw [moduleRefinementExchangeIso_hom_app, normalized_left_identity_app]
  exact moduleBaseChangeMap_identity_source_id i h.w Λ M

/-- Composition of identity-source exchanges uses the original direct-image comparison. -/
theorem moduleRefinementExchangeIso_comp {U Z Y X : Scheme.{u}}
    (i : U ⟶ Z) (j : U ⟶ Y) (l : U ⟶ X) (f : Y ⟶ X) (k : Z ⟶ Y)
    [Etale j] [Etale l]
    (hf : IsPullback (𝟙 U) j l f) (hk : IsPullback (𝟙 U) i j k)
    (ht : IsPullback (𝟙 U) i l (k ≫ f)) (Λ : Type (u + 1)) [Ring Λ] :
    moduleRefinementExchangeIso i l (k ≫ f) ht Λ =
      Functor.isoWhiskerRight (moduleDirectImageCompIso Λ f k) (moduleInverseImage l Λ) ≪≫
        Functor.associator (moduleDirectImage k Λ) (moduleDirectImage f Λ)
          (moduleInverseImage l Λ) ≪≫
        Functor.isoWhiskerLeft (moduleDirectImage k Λ)
          (moduleRefinementExchangeIso j l f hf Λ) ≪≫
        moduleRefinementExchangeIso i j k hk Λ := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  rw [adjusted_composition_app]
  simp only [moduleRefinementExchangeIso_hom_app]
  simpa only [CategoryTheory.Category.assoc] using
    moduleBaseChangeMap_identity_source_comp i j l f k hf.w hk.w ht.w Λ M

end AlgebraicGeometry.Scheme.EtaleCohomology
