/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChange

/-! # Interchange of the original higher exchanges on relative charts

Two applications of the original horizontal-pasting equality give the square
between a base-change map and its chart-relative base-change map. Both
coefficient comparisons are the original inverse-image square isomorphisms.
The eight derived models are independent; no Cartesian or invertibility
condition is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

private theorem interchange_of_pastings {C : Type*} [Category* C]
    {A B S₁ S₂ T₁ T₂ D E : C}
    (a : S₁ ≅ A) (b : S₂ ≅ B) (s : S₂ ≅ S₁)
    (c : T₁ ≅ D) (d : T₂ ≅ E) (t : T₂ ≅ T₁)
    (p : A ⟶ D) (q : B ⟶ E) (v : S₁ ⟶ T₁) (w : S₂ ⟶ T₂)
    (hp : a.hom ≫ p = v ≫ c.hom)
    (hq : b.hom ≫ q = w ≫ d.hom)
    (h : s.inv ≫ w = v ≫ t.inv) :
    (a.inv ≫ s.inv ≫ b.hom) ≫ q = p ≫ (c.inv ≫ t.inv ≫ d.hom) := by
  calc
    _ = a.inv ≫ s.inv ≫ (b.hom ≫ q) := by simp only [Category.assoc]
    _ = a.inv ≫ s.inv ≫ (w ≫ d.hom) := by rw [hq]
    _ = a.inv ≫ (s.inv ≫ w) ≫ d.hom := by simp only [Category.assoc]
    _ = a.inv ≫ (v ≫ t.inv) ≫ d.hom := by rw [h]
    _ = (a.inv ≫ (v ≫ c.hom)) ≫ c.inv ≫ t.inv ≫ d.hom := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = (a.inv ≫ (a.hom ≫ p)) ≫ c.inv ≫ t.inv ≫ d.hom := by rw [hp]
    _ = _ := by simp only [Iso.inv_hom_id_assoc]

private theorem mapped_interchange_of_pastings {C D : Type*} [Category* C] [Category* D]
    (R : C ⥤ D) {A B S₁ S₂ M N : D} {T₁ T₂ P Q : C}
    (a : S₁ ≅ A) (b : S₂ ≅ B) (s : S₂ ≅ S₁)
    (c : T₁ ≅ P) (d : T₂ ≅ Q) (t : T₂ ≅ T₁)
    (α : A ⟶ B) (δ : P ⟶ Q)
    (hα : α = a.inv ≫ s.inv ≫ b.hom)
    (hδ : δ = c.inv ≫ t.inv ≫ d.hom)
    (p₁ : A ⟶ M) (p₂ : M ⟶ R.obj P) (q₁ : B ⟶ N) (q₂ : N ⟶ R.obj Q)
    (v : S₁ ⟶ R.obj T₁) (w : S₂ ⟶ R.obj T₂)
    (hp : a.hom ≫ p₁ ≫ p₂ = v ≫ R.map c.hom)
    (hq : b.hom ≫ q₁ ≫ q₂ = w ≫ R.map d.hom)
    (ht : s.inv ≫ w = v ≫ R.map t.inv) :
    α ≫ q₁ ≫ q₂ = p₁ ≫ p₂ ≫ R.map δ := by
  have h := interchange_of_pastings a b s (R.mapIso c) (R.mapIso d) (R.mapIso t)
    (p₁ ≫ p₂) (q₁ ≫ q₂) v w hp hq ht
  rw [hα, hδ]
  simpa only [Functor.mapIso_inv, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc] using h

private theorem natIso_inverse_factor_app {C D : Type*} [Category* C] [Category* D]
    {P Q R S : C ⥤ D} (e : P ≅ Q) (a : R ≅ P) (b : R ≅ S) (c : S ≅ Q)
    (h : e = a.symm ≪≫ b ≪≫ c) (F : C) :
    e.inv.app F = (c.app F).inv ≫ (b.app F).inv ≫ (a.app F).hom := by
  rw [h]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Iso.app_inv, Iso.app_hom,
    Category.assoc]

private theorem natIso_inverse_factor {C D : Type*} [Category* C] [Category* D]
    {P Q R S : C ⥤ D} (e : P ≅ Q) (a : R ≅ P) (b : R ≅ S) (c : S ≅ Q)
    (h : e = a.symm ≪≫ b ≪≫ c) : e.inv = c.inv ≫ b.inv ≫ a.hom := by
  rw [h]
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]

private theorem natMapped_interchange_of_pastings
    {C₀ C₁ D₀ D₁ : Type*} [Category* C₀] [Category* C₁]
    [Category* D₀] [Category* D₁] (L : C₀ ⥤ D₀) (R : C₁ ⥤ D₁)
    {A B S₁ S₂ : D₀ ⥤ D₁} {T₁ T₂ P Q : C₀ ⥤ C₁} {M N : C₀ ⥤ D₁}
    (a : S₁ ≅ A) (b : S₂ ≅ B) (s : S₂ ≅ S₁)
    (c : T₁ ≅ P) (d : T₂ ≅ Q) (t : T₂ ≅ T₁)
    (α : A ⟶ B) (δ : P ⟶ Q)
    (hα : α = a.inv ≫ s.inv ≫ b.hom)
    (hδ : δ = c.inv ≫ t.inv ≫ d.hom)
    (p₁ : L ⋙ A ⟶ M) (p₂ : M ⟶ P ⋙ R)
    (q₁ : L ⋙ B ⟶ N) (q₂ : N ⟶ Q ⋙ R)
    (v : L ⋙ S₁ ⟶ T₁ ⋙ R) (w : L ⋙ S₂ ⟶ T₂ ⋙ R)
    (hp : ∀ F, a.hom.app (L.obj F) ≫ p₁.app F ≫ p₂.app F =
      v.app F ≫ R.map (c.hom.app F))
    (hq : ∀ F, b.hom.app (L.obj F) ≫ q₁.app F ≫ q₂.app F =
      w.app F ≫ R.map (d.hom.app F))
    (ht : ∀ F, s.inv.app (L.obj F) ≫ w.app F =
      v.app F ≫ R.map (t.inv.app F)) (F : C₀) :
    α.app (L.obj F) ≫ q₁.app F ≫ q₂.app F =
      p₁.app F ≫ p₂.app F ≫ R.map (δ.app F) := by
  have hαF : α.app (L.obj F) =
      (a.app (L.obj F)).inv ≫ (s.app (L.obj F)).inv ≫ (b.app (L.obj F)).hom := by
    simpa only [NatTrans.comp_app, Iso.app_inv, Iso.app_hom] using
      NatTrans.congr_app hα (L.obj F)
  have hδF : δ.app F = (c.app F).inv ≫ (t.app F).inv ≫ (d.app F).hom := by
    simpa only [NatTrans.comp_app, Iso.app_inv, Iso.app_hom] using NatTrans.congr_app hδ F
  exact mapped_interchange_of_pastings R
    (a.app (L.obj F)) (b.app (L.obj F)) (s.app (L.obj F))
    (c.app F) (d.app F) (t.app F) (α.app (L.obj F)) (δ.app F) hαF hδF
    (p₁.app F) (p₂.app F) (q₁.app F) (q₂.app F) (v.app F) (w.app F)
    (hp F) (hq F) (ht F)

private theorem exchangeFamily_transport
    {A B : Sort*} {CX CS CY CT : Type*}
    [Category* CX] [Category* CS] [Category* CY] [Category* CT]
    (P : A → CS ⥤ CT) (Q : B → CX ⥤ CY) (L : CX ⥤ CS) (R : CY ⥤ CT)
    (H : A → B → Prop) (β : ∀ a k, H a k → (L ⋙ P a ⟶ Q k ⋙ R))
    (a₁ a₂ : A) (k₁ k₂ : B) (h₁ : H a₁ k₁) (h₂ : H a₂ k₂)
    (ha : a₂ = a₁) (hk : k₂ = k₁) (F : CX) :
    (eqToIso (congrArg P ha)).inv.app (L.obj F) ≫ (β a₂ k₂ h₂).app F =
      (β a₁ k₁ h₁).app F ≫ R.map ((eqToIso (congrArg Q hk)).inv.app F) := by
  subst a₂
  subst k₂
  simp only [eqToIso_refl, Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  rw [R.map_id ((Q k₁).obj F)]
  exact (Category.comp_id ((β a₁ k₁ h₁).app F)).symm

universe u dX dS dX' dS' dZ dU dW dV

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

private theorem inverseImageSquareIso_inv_factor {X S Y T : Scheme.{u}}
    (f : X ⟶ S) (fT : Y ⟶ T) (a : T ⟶ S) (k : Y ⟶ X)
    (h : fT ≫ a = k ≫ f) (F : AbelianSheaf.{u, u + 1} S) :
    (inverseImageSquareIso f fT a k h).inv.app F =
      ((inverseImageComp f k).app F).inv ≫
        ((eqToIso (congrArg (fun l : Y ⟶ S => inverseImage l) h)).app F).inv ≫
        ((inverseImageComp a fT).app F).hom := by
  exact natIso_inverse_factor_app (inverseImageSquareIso f fT a k h)
    (inverseImageComp a fT)
    (eqToIso (congrArg (fun l : Y ⟶ S => inverseImage l) h)) (inverseImageComp f k)
    (inverseImageSquareIso_eq_comp f fT a k h) F

private theorem inverseImageSquareIso_inv_factor_whole {X S Y T : Scheme.{u}}
    (f : X ⟶ S) (fT : Y ⟶ T) (a : T ⟶ S) (k : Y ⟶ X)
    (h : fT ≫ a = k ≫ f) :
    (inverseImageSquareIso f fT a k h).inv =
      (inverseImageComp f k).inv ≫
        (eqToIso (congrArg (fun l : Y ⟶ S => inverseImage l) h)).inv ≫
        (inverseImageComp a fT).hom :=
  natIso_inverse_factor (inverseImageSquareIso f fT a k h) (inverseImageComp a fT)
    (eqToIso (congrArg (fun l : Y ⟶ S => inverseImage l) h)) (inverseImageComp f k)
    (inverseImageSquareIso_eq_comp f fT a k h)

private theorem higherBaseChangeMap_transport
    {X S Y T : Scheme.{u}}
    [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{dW} (AbelianSheaf.{u, u + 1} Y)]
    [HasDerivedCategory.{dV} (AbelianSheaf.{u, u + 1} T)]
    (f : X ⟶ S) (fT : Y ⟶ T) (a₁ a₂ : T ⟶ S) (k₁ k₂ : Y ⟶ X)
    (h₁ : fT ≫ a₁ = k₁ ≫ f) (h₂ : fT ≫ a₂ = k₂ ≫ f)
    (ha : a₂ = a₁) (hk : k₂ = k₁) (q : ℕ) (F : AbelianSheaf.{u, u + 1} X) :
    (eqToIso (congrArg (fun a : T ⟶ S => inverseImage a) ha)).inv.app
        ((higherDirectImage f q).obj F) ≫
        (higherBaseChangeMap f fT a₂ k₂ h₂ q).app F =
      (higherBaseChangeMap f fT a₁ k₁ h₁ q).app F ≫
        (higherDirectImage fT q).map
          ((eqToIso (congrArg (fun k : Y ⟶ X => inverseImage k) hk)).inv.app F) := by
  exact exchangeFamily_transport
    (fun a : T ⟶ S => inverseImage a) (fun k : Y ⟶ X => inverseImage k)
    (higherDirectImage f q) (higherDirectImage fT q)
    (fun a k => fT ≫ a = k ≫ f)
    (fun a k h => higherBaseChangeMap f fT a k h q) a₁ a₂ k₁ k₂ h₁ h₂ ha hk F

variable {X S X' S' Z U W V : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  [HasDerivedCategory.{dZ} (AbelianSheaf.{u, u + 1} Z)]
  [HasDerivedCategory.{dU} (AbelianSheaf.{u, u + 1} U)]
  [HasDerivedCategory.{dW} (AbelianSheaf.{u, u + 1} W)]
  [HasDerivedCategory.{dV} (AbelianSheaf.{u, u + 1} V)]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)
  (fU : Z ⟶ U) (fV : W ⟶ V) (aU : U ⟶ S) (aV : V ⟶ S')
  (piU : Z ⟶ X) (piV : W ⟶ X') (b : V ⟶ U) (r : W ⟶ Z)
  (hU : fU ≫ aU = piU ≫ f) (hV : fV ≫ aV = piV ≫ f')
  (hb : aV ≫ g = b ≫ aU) (hr : piV ≫ g' = r ≫ piU)
  (hR : fV ≫ b = r ≫ fU)

/-- Interchange of the original higher exchanges, with the two literal
inverse-image square comparisons and every original coefficient map retained. -/
theorem higherBaseChangeMap_chartRelative_square (q : ℕ)
    (F : AbelianSheaf.{u, u + 1} X) :
    (inverseImageSquareIso aU aV g b hb).inv.app ((higherDirectImage f q).obj F) ≫
        (inverseImage aV).map ((higherBaseChangeMap f f' g g' h q).app F) ≫
        (higherBaseChangeMap f' fV aV piV hV q).app ((inverseImage g').obj F) =
      (inverseImage b).map ((higherBaseChangeMap f fU aU piU hU q).app F) ≫
        (higherBaseChangeMap fU fV b r hR q).app ((inverseImage piU).obj F) ≫
        (higherDirectImage fV q).map ((inverseImageSquareIso piU piV g' r hr).inv.app F) := by
  let h₁ : fV ≫ (b ≫ aU) = (r ≫ piU) ≫ f := by
    rw [← Category.assoc, hR, Category.assoc, hU, ← Category.assoc]
  let h₂ : fV ≫ (aV ≫ g) = (piV ≫ g') ≫ f := by
    rw [← Category.assoc, hV, Category.assoc, h, ← Category.assoc]
  exact natMapped_interchange_of_pastings (higherDirectImage f q) (higherDirectImage fV q)
    (inverseImageComp aU b) (inverseImageComp g aV)
    (eqToIso (congrArg (fun a : V ⟶ S => inverseImage a) hb))
    (inverseImageComp piU r) (inverseImageComp g' piV)
    (eqToIso (congrArg (fun k : W ⟶ X => inverseImage k) hr))
    (inverseImageSquareIso aU aV g b hb).inv
    (inverseImageSquareIso piU piV g' r hr).inv
    (inverseImageSquareIso_inv_factor_whole aU aV g b hb)
    (inverseImageSquareIso_inv_factor_whole piU piV g' r hr)
    (Functor.whiskerRight (higherBaseChangeMap f fU aU piU hU q) (inverseImage b))
    (Functor.whiskerLeft (inverseImage piU) (higherBaseChangeMap fU fV b r hR q))
    (Functor.whiskerRight (higherBaseChangeMap f f' g g' h q) (inverseImage aV))
    (Functor.whiskerLeft (inverseImage g') (higherBaseChangeMap f' fV aV piV hV q))
    (higherBaseChangeMap f fV (b ≫ aU) (r ≫ piU) h₁ q)
    (higherBaseChangeMap f fV (aV ≫ g) (piV ≫ g') h₂ q)
    (fun E => higherBaseChangeMap_hComp f fU fV aU b piU r hU hR h₁ q E)
    (fun E => higherBaseChangeMap_hComp f f' fV g aV g' piV h hV h₂ q E)
    (fun E => higherBaseChangeMap_transport f fV (b ≫ aU) (aV ≫ g)
      (r ≫ piU) (piV ≫ g') h₁ h₂ hb hr q E) F

end AlgebraicGeometry.Scheme.EtaleCohomology
