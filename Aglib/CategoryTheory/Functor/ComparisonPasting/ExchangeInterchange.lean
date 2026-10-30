/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ComparisonPasting
public import Aglib.CategoryTheory.Adjunction.Mates.Whole

/-! # Noninvertible exchange interchange from original pastings

The full finite rectangle retains its original exchange arrows. Comparison
isomorphisms and equality transports supply the outer frame, and the two
original pasting laws prove the whole relative TwoSquare equality.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.ExchangeInterchange

/-- Two original pasting laws imply the noninvertible outer interchange. -/
theorem interchange_of_pastings {C : Type*} [Category* C]
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

/-- The inverse of the original three-factor natural isomorphism has the reverse factors. -/
theorem natIso_inverse_factor {C D : Type*} [Category* C] [Category* D]
    {P Q R S : C ⥤ D} (e : P ≅ Q) (a : R ≅ P) (b : R ≅ S) (c : S ≅ Q)
    (h : e = a.symm ≪≫ b ≪≫ c) : e.inv = c.inv ≫ b.inv ≫ a.hom := by
  rw [h]
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]

/-- Whiskering preserves the whole noninvertible original interchange. -/
theorem natMapped_interchange_of_pastings_whole
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

/-- Equality transport preserves the original indexed exchange family. -/
theorem exchangeFamily_transport_whole
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

/-- A whole exchange equation gives the same relative TwoSquare equality. -/
theorem twoSquare_relative_of_whole
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

/-- Whole relative exchange from the two original pastings and their source
transport. Only the displayed comparison edges are isomorphisms. -/
theorem twoSquare_relative_of_pastings
    {CX CS CX' CS' CZ CU CW CV : Type*}
    [Category* CX] [Category* CS] [Category* CX'] [Category* CS']
    [Category* CZ] [Category* CU] [Category* CW] [Category* CV]
    {P : CX ⥤ CS} {P' : CX' ⥤ CS'} {PU : CZ ⥤ CU} {PV : CW ⥤ CV}
    {Ig : CS ⥤ CS'} {Ig' : CX ⥤ CX'} {IU : CS ⥤ CU} {IV : CS' ⥤ CV}
    {IpiU : CX ⥤ CZ} {IpiV : CX' ⥤ CW} {Ib : CU ⥤ CV} {Ir : CZ ⥤ CW}
    {β : TwoSquare P Ig' Ig P'} {βU : TwoSquare P IpiU IU PU}
    {βV : TwoSquare P' IpiV IV PV} {βR : TwoSquare PU Ir Ib PV}
    {S₁ S₂ : CS ⥤ CV} {T₁ T₂ : CX ⥤ CW}
    (a : S₁ ≅ IU ⋙ Ib) (b : S₂ ≅ Ig ⋙ IV) (s : S₂ ≅ S₁)
    (c : T₁ ≅ IpiU ⋙ Ir) (d : T₂ ≅ Ig' ⋙ IpiV) (t : T₂ ≅ T₁)
    (δS : IU ⋙ Ib ⟶ Ig ⋙ IV) (δX : IpiU ⋙ Ir ⟶ Ig' ⋙ IpiV)
    (hδS : δS = a.inv ≫ s.inv ≫ b.hom)
    (hδX : δX = c.inv ≫ t.inv ≫ d.hom)
    (v : P ⋙ S₁ ⟶ T₁ ⋙ PV) (w : P ⋙ S₂ ⟶ T₂ ⋙ PV)
    (hp : Functor.whiskerLeft P a.hom ≫
        Functor.whiskerRight βU.natTrans Ib ≫ Functor.whiskerLeft IpiU βR.natTrans =
      v ≫ Functor.whiskerRight c.hom PV)
    (hq : Functor.whiskerLeft P b.hom ≫
        Functor.whiskerRight β.natTrans IV ≫ Functor.whiskerLeft Ig' βV.natTrans =
      w ≫ Functor.whiskerRight d.hom PV)
    (ht : Functor.whiskerLeft P s.inv ≫ w =
      v ≫ Functor.whiskerRight t.inv PV) :
    (β.vComp βV).whiskerRight δS = (βU.vComp βR).whiskerLeft δX := by
  apply twoSquare_relative_of_whole
  exact natMapped_interchange_of_pastings_whole P PV a b s c d t δS δX hδS hδX
    (Functor.whiskerRight βU.natTrans Ib) (Functor.whiskerLeft IpiU βR.natTrans)
    (Functor.whiskerRight β.natTrans IV) (Functor.whiskerLeft Ig' βV.natTrans)
    v w hp hq ht

end CategoryTheory.ExchangeInterchange
