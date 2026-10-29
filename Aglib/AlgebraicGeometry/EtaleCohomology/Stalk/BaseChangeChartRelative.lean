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

The ordinary square is intrinsic. Separate compatibility companions retain the
literal original transports in all eight independently supplied derived models.
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

private theorem natIso_inverse_factor {C D : Type*} [Category* C] [Category* D]
    {P Q R S : C ⥤ D} (e : P ≅ Q) (a : R ≅ P) (b : R ≅ S) (c : S ≅ Q)
    (h : e = a.symm ≪≫ b ≪≫ c) : e.inv = c.inv ≫ b.inv ≫ a.hom := by
  rw [h]
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]

private theorem natMapped_interchange_of_pastings_whole
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
    (hp : Functor.whiskerLeft L a.hom ≫ p₁ ≫ p₂ =
      v ≫ Functor.whiskerRight c.hom R)
    (hq : Functor.whiskerLeft L b.hom ≫ q₁ ≫ q₂ =
      w ≫ Functor.whiskerRight d.hom R)
    (ht : Functor.whiskerLeft L s.inv ≫ w =
      v ≫ Functor.whiskerRight t.inv R) :
    Functor.whiskerLeft L α ≫ q₁ ≫ q₂ =
      p₁ ≫ p₂ ≫ Functor.whiskerRight δ R := by
  have h := interchange_of_pastings
    (Functor.isoWhiskerLeft L a) (Functor.isoWhiskerLeft L b)
    (Functor.isoWhiskerLeft L s) (Functor.isoWhiskerRight c R)
    (Functor.isoWhiskerRight d R) (Functor.isoWhiskerRight t R)
    (p₁ ≫ p₂) (q₁ ≫ q₂) v w hp hq ht
  rw [hα, hδ]
  simpa only [Functor.isoWhiskerLeft_inv, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Category.assoc] using h

private theorem exchangeFamily_transport_whole
    {A B : Sort*} {CX CS CY CT : Type*}
    [Category* CX] [Category* CS] [Category* CY] [Category* CT]
    (P : A → CS ⥤ CT) (Q : B → CX ⥤ CY) (L : CX ⥤ CS) (R : CY ⥤ CT)
    (H : A → B → Prop) (β : ∀ a k, H a k → (L ⋙ P a ⟶ Q k ⋙ R))
    (a₁ a₂ : A) (k₁ k₂ : B) (h₁ : H a₁ k₁) (h₂ : H a₂ k₂)
    (ha : a₂ = a₁) (hk : k₂ = k₁) :
    Functor.whiskerLeft L (eqToIso (congrArg P ha)).inv ≫ β a₂ k₂ h₂ =
      β a₁ k₁ h₁ ≫ Functor.whiskerRight (eqToIso (congrArg Q hk)).inv R := by
  subst a₂
  subst k₂
  simp only [eqToIso_refl, Iso.refl_inv, Functor.whiskerLeft_id',
    Functor.whiskerRight_id', Category.id_comp, Category.comp_id]

private theorem twoSquare_relative_of_whole
    {CX CS CX' CS' CZ CU CW CV : Type*}
    [Category* CX] [Category* CS] [Category* CX'] [Category* CS']
    [Category* CZ] [Category* CU] [Category* CW] [Category* CV]
    {P : CX ⥤ CS} {P' : CX' ⥤ CS'} {PU : CZ ⥤ CU} {PV : CW ⥤ CV}
    {Ig : CS ⥤ CS'} {Ig' : CX ⥤ CX'} {IU : CS ⥤ CU} {IV : CS' ⥤ CV}
    {IpiU : CX ⥤ CZ} {IpiV : CX' ⥤ CW} {Ib : CU ⥤ CV} {Ir : CZ ⥤ CW}
    (β : TwoSquare P Ig' Ig P') (βU : TwoSquare P IpiU IU PU)
    (βV : TwoSquare P' IpiV IV PV) (βR : TwoSquare PU Ir Ib PV)
    (δS : IU ⋙ Ib ⟶ Ig ⋙ IV) (δX : IpiU ⋙ Ir ⟶ Ig' ⋙ IpiV)
    (h : Functor.whiskerLeft P δS ≫ Functor.whiskerRight β.natTrans IV ≫
        Functor.whiskerLeft Ig' βV.natTrans =
      Functor.whiskerRight βU.natTrans Ib ≫ Functor.whiskerLeft IpiU βR.natTrans ≫
        Functor.whiskerRight δX PV) :
    (β.vComp βV).whiskerRight δS = (βU.vComp βR).whiskerLeft δX := by
  apply TwoSquare.ext
  intro F
  simpa only [TwoSquare.whiskerRight_app, TwoSquare.whiskerLeft_app,
    TwoSquare.vComp_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc] using NatTrans.congr_app h F

universe u dX dS dX' dS' dZ dU dW dV

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

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

private theorem higherBaseChangeMap_transport_whole
    {X S Y T : Scheme.{u}}
            (f : X ⟶ S) (fT : Y ⟶ T) (a₁ a₂ : T ⟶ S) (k₁ k₂ : Y ⟶ X)
    (h₁ : fT ≫ a₁ = k₁ ≫ f) (h₂ : fT ≫ a₂ = k₂ ≫ f)
    (ha : a₂ = a₁) (hk : k₂ = k₁) (q : ℕ) :
    Functor.whiskerLeft (higherDirectImage f q)
        (eqToIso (congrArg (fun a : T ⟶ S => inverseImage a) ha)).inv ≫
        higherBaseChangeMap f fT a₂ k₂ h₂ q =
      higherBaseChangeMap f fT a₁ k₁ h₁ q ≫
        Functor.whiskerRight
          (eqToIso (congrArg (fun k : Y ⟶ X => inverseImage k) hk)).inv
          (higherDirectImage fT q) :=
  exchangeFamily_transport_whole
    (fun a : T ⟶ S => inverseImage a) (fun k : Y ⟶ X => inverseImage k)
    (higherDirectImage f q) (higherDirectImage fT q)
    (fun a k => fT ≫ a = k ≫ f)
    (fun a k h => higherBaseChangeMap f fT a k h q) a₁ a₂ k₁ k₂ h₁ h₂ ha hk

section Ordinary

variable {X S X' S' Z U W V : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)
  (fU : Z ⟶ U) (fV : W ⟶ V) (aU : U ⟶ S) (aV : V ⟶ S')
  (piU : Z ⟶ X) (piV : W ⟶ X') (b : V ⟶ U) (r : W ⟶ Z)
  (hU : fU ≫ aU = piU ≫ f) (hV : fV ≫ aV = piV ≫ f')
  (hb : aV ≫ g = b ≫ aU) (hr : piV ≫ g' = r ≫ piU)
  (hR : fV ≫ b = r ≫ fU)

/-- Whole interchange of the four original higher exchanges, before a coefficient
is chosen. Both comparisons are the original inverse-image square isomorphisms,
with an intrinsic ordinary higher map at every edge. -/
theorem higherBaseChangeMap_chartRelative_square_whole (q : ℕ) :
    ((TwoSquare.mk (higherDirectImage f q) (inverseImage g') (inverseImage g)
        (higherDirectImage f' q) (higherBaseChangeMap f f' g g' h q)).vComp
      (TwoSquare.mk (higherDirectImage f' q) (inverseImage piV) (inverseImage aV)
        (higherDirectImage fV q) (higherBaseChangeMap f' fV aV piV hV q))).whiskerRight
          (inverseImageSquareIso aU aV g b hb).inv =
      ((TwoSquare.mk (higherDirectImage f q) (inverseImage piU) (inverseImage aU)
        (higherDirectImage fU q) (higherBaseChangeMap f fU aU piU hU q)).vComp
      (TwoSquare.mk (higherDirectImage fU q) (inverseImage r) (inverseImage b)
        (higherDirectImage fV q) (higherBaseChangeMap fU fV b r hR q))).whiskerLeft
          (inverseImageSquareIso piU piV g' r hr).inv := by
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X')
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S')
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} Z)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} U)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} W)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} V)
  let h₁ : fV ≫ (b ≫ aU) = (r ≫ piU) ≫ f := by
    rw [← Category.assoc, hR, Category.assoc, hU, ← Category.assoc]
  let h₂ : fV ≫ (aV ≫ g) = (piV ≫ g') ≫ f := by
    rw [← Category.assoc, hV, Category.assoc, h, ← Category.assoc]
  apply twoSquare_relative_of_whole
  exact natMapped_interchange_of_pastings_whole (higherDirectImage f q)
    (higherDirectImage fV q)
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
    (higherHorizontalWholeLadder_pasting f fU fV aU b piU r hU hR h₁ q)
    (higherHorizontalWholeLadder_pasting f f' fV g aV g' piV h hV h₂ q)
    (higherBaseChangeMap_transport_whole f fV (b ≫ aU) (aV ≫ g)
      (r ≫ piU) (piV ≫ g') h₁ h₂ hb hr q)

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
  have hwhole := higherBaseChangeMap_chartRelative_square_whole
    f f' g g' h fU fV aU aV piU piV b r hU hV hb hr hR q
  simpa only [TwoSquare.whiskerRight_app, TwoSquare.whiskerLeft_app,
    TwoSquare.vComp_app, TwoSquare.mk, TwoSquare.natTrans, Category.assoc] using
    NatTrans.congr_app hwhole F

end Ordinary

section SelectedModels

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

/-- The literal original relative square in all eight independently selected models. -/
theorem higherBaseChangeMapFromDerived_chartRelative_square_whole (q : ℕ) :
    ((TwoSquare.mk (higherDirectImage f q) (inverseImage g') (inverseImage g)
        (higherDirectImage f' q) (higherBaseChangeMapFromDerived f f' g g' h q)).vComp
      (TwoSquare.mk (higherDirectImage f' q) (inverseImage piV) (inverseImage aV)
        (higherDirectImage fV q) (higherBaseChangeMapFromDerived f' fV aV piV hV q))).whiskerRight
          (inverseImageSquareIso aU aV g b hb).inv =
      ((TwoSquare.mk (higherDirectImage f q) (inverseImage piU) (inverseImage aU)
        (higherDirectImage fU q) (higherBaseChangeMapFromDerived f fU aU piU hU q)).vComp
      (TwoSquare.mk (higherDirectImage fU q) (inverseImage r) (inverseImage b)
        (higherDirectImage fV q) (higherBaseChangeMapFromDerived fU fV b r hR q))).whiskerLeft
          (inverseImageSquareIso piU piV g' r hr).inv := by
  simpa only [higherBaseChangeMapFromDerived_eq] using
    higherBaseChangeMap_chartRelative_square_whole
      f f' g g' h fU fV aU aV piU piV b r hU hV hb hr hR q

/-- The original selected-model relative square retains every coefficient component. -/
theorem higherBaseChangeMapFromDerived_chartRelative_square (q : ℕ)
    (F : AbelianSheaf.{u, u + 1} X) :
    (inverseImageSquareIso aU aV g b hb).inv.app ((higherDirectImage f q).obj F) ≫
        (inverseImage aV).map ((higherBaseChangeMapFromDerived f f' g g' h q).app F) ≫
        (higherBaseChangeMapFromDerived f' fV aV piV hV q).app ((inverseImage g').obj F) =
      (inverseImage b).map ((higherBaseChangeMapFromDerived f fU aU piU hU q).app F) ≫
        (higherBaseChangeMapFromDerived fU fV b r hR q).app ((inverseImage piU).obj F) ≫
        (higherDirectImage fV q).map ((inverseImageSquareIso piU piV g' r hr).inv.app F) := by
  simpa only [higherBaseChangeMapFromDerived_eq] using
    higherBaseChangeMap_chartRelative_square f f' g g' h fU fV aU aV piU piV b r hU hV hb hr hR q F

end SelectedModels

end AlgebraicGeometry.Scheme.EtaleCohomology
