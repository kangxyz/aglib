/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.UnderlyingEquivalence
public import Aglib.CategoryTheory.Adjunction.Mates.ScalarForgettingCoherence
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Whiskering

/-! # Original comparisons between coefficient presentations

The original inverse-equivalence comparison is constructed as a whole natural
isomorphism. Its unit proof uses the actual right transport value and original
left-comparison unit law. Fully faithful transport constructs the actual
exchange and proves its whole value before components are evaluated.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.ValuedComparison

section Units

variable {C D A B : Type*} [Category* C] [Category* D] [Category* A] [Category* B]

/-- The actual inverse-equivalence comparison from the original left transport. -/
def inverseValuedIso (E : C ≌ A) (F : D ≌ B) {L : C ⥤ D} {Lₙ : A ⥤ B}
    (eL : Lₙ ≅ (E.inverse ⋙ L) ⋙ F.functor) :
    Lₙ ⋙ F.inverse ≅ E.inverse ⋙ L :=
  Functor.isoWhiskerRight eL _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ F.unitIso.symm ≪≫ Functor.rightUnitor _

/-- The original right transport cancels through the original inverse-equivalence unit. -/
theorem rightInverse_comparison (E : C ≌ A) (Rₙ : B ⥤ A) (I : B ⥤ D) (R : D ⥤ C)
    (q : Rₙ ⋙ E.inverse ≅ I ⋙ R) (eR : Rₙ ≅ I ⋙ R ⋙ E.functor)
    (heR : ∀ M, eR.inv.app M =
      E.functor.map (q.inv.app M) ≫ E.counitIso.hom.app (Rₙ.obj M)) (M : B) :
    E.inverse.map (eR.inv.app M) ≫ q.hom.app M =
      E.unitIso.inv.app (R.obj (I.obj M)) := by
  have hk : (eR).inv.app M =
      E.functor.map ((q).inv.app M) ≫
        E.counitIso.hom.app ((Rₙ).obj M) :=
    heR M
  rw [hk, Functor.map_comp]
  change (E.inverse.map (E.functor.map _) ≫ E.inverse.map (E.counit.app _)) ≫ _ = _
  rw [← E.unitInv_app_inverse]
  have hn := E.unitIso.inv.naturality ((q).inv.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  change (E.inverse.map (E.functor.map _) ≫ E.unitIso.inv.app _) ≫ _ = _
  rw [hn]
  simp only [Functor.id_map, Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj,
    ]
  exact Category.comp_id _

/-- The actual composed and right-transported adjunction retains its valued unit. -/
theorem transportUnit_comparison (E : C ≌ A) (F : D ≌ B)
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (Rₙ : B ⥤ A)
    (q : Rₙ ⋙ E.inverse ≅ F.inverse ⋙ R)
    (eR : Rₙ ≅ F.inverse ⋙ R ⋙ E.functor)
    (heR : ∀ M, eR.inv.app M =
      E.functor.map (q.inv.app M) ≫ E.counitIso.hom.app (Rₙ.obj M)) (M : A) :
    E.inverse.map
        ((((E.symm.toAdjunction.comp a).comp F.toAdjunction).ofNatIsoRight eR.symm).unit.app M) ≫
      q.hom.app ((((E.inverse ⋙ L) ⋙ F.functor).obj M)) =
    a.unit.app (E.inverse.obj M) ≫ R.map (F.unitIso.hom.app (L.obj (E.inverse.obj M))) := by
  let EX := E
  let ES := F
  let η := (a).unit
  change EX.inverse.map
      ((((EX.symm.toAdjunction.comp (a)).comp
        ES.toAdjunction).unit.app M) ≫
        (eR).inv.app
          (ES.functor.obj (L.obj (EX.inverse.obj M)))) ≫ _ = _
  rw [Functor.map_comp, Category.assoc]
  have hk := rightInverse_comparison E Rₙ F.inverse R q eR heR
    (ES.functor.obj (L.obj (EX.inverse.obj M)))
  change EX.inverse.map _ ≫
      (EX.inverse.map ((eR).inv.app
        (ES.functor.obj (L.obj (EX.inverse.obj M)))) ≫
      (q).hom.app
        (ES.functor.obj (L.obj (EX.inverse.obj M)))) = _
  rw [hk]
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  change EX.inverse.map ((EX.counitIso.inv.app M ≫
      EX.functor.map (η.app (EX.inverse.obj M))) ≫
      EX.functor.map (R.map (ES.unitIso.hom.app (L.obj (EX.inverse.obj M))))) ≫
    EX.unitIso.inv.app (R.obj (ES.inverse.obj (ES.functor.obj
      (L.obj (EX.inverse.obj M))))) =
    η.app (EX.inverse.obj M) ≫ R.map (ES.unitIso.hom.app (L.obj (EX.inverse.obj M)))
  rw [Functor.map_comp, Functor.map_comp, ← EX.unit_app_inverse]
  change ((EX.unit.app (EX.inverse.obj M) ≫
      EX.inverse.map (EX.functor.map (η.app (EX.inverse.obj M)))) ≫
      EX.inverse.map (EX.functor.map (R.map
        (ES.unitIso.hom.app (L.obj (EX.inverse.obj M)))))) ≫
    EX.unitIso.inv.app (R.obj (ES.inverse.obj (ES.functor.obj
      (L.obj (EX.inverse.obj M))))) = _
  have hη := EX.unit_naturality (η.app (EX.inverse.obj M))
  have hu := EX.unit_naturality (R.map (ES.unitIso.hom.app (L.obj (EX.inverse.obj M))))
  simp only [Functor.comp_obj, Functor.id_obj] at hη hu
  change EX.unit.app (EX.inverse.obj M) ≫
      EX.inverse.map (EX.functor.map (η.app (EX.inverse.obj M))) =
    η.app (EX.inverse.obj M) ≫ EX.unit.app (R.obj (L.obj (EX.inverse.obj M))) at hη
  have hc := congrArg (fun a => a ≫ EX.unitIso.inv.app
    (R.obj (ES.inverse.obj (ES.functor.obj (L.obj (EX.inverse.obj M)))))) hu
  simp only [Category.assoc, Iso.hom_inv_id_app] at hc
  rw [hη]
  simp only [Category.assoc]
  rw [hc]
  exact congrArg (fun a => η.app (EX.inverse.obj M) ≫ a) (Category.comp_id _)

/-- The specified native left unit becomes the original valued unit through the
constructed inverse-equivalence comparison. -/
theorem inverseValuedIso_unit (E : C ≌ A) (F : D ≌ B)
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    {Lₙ : A ⥤ B} {Rₙ : B ⥤ A} (b : Lₙ ⊣ Rₙ)
    (q : Rₙ ⋙ E.inverse ≅ F.inverse ⋙ R)
    (eR : Rₙ ≅ F.inverse ⋙ R ⋙ E.functor)
    (eL : Lₙ ≅ (E.inverse ⋙ L) ⋙ F.functor)
    (heR : ∀ M, eR.inv.app M =
      E.functor.map (q.inv.app M) ≫ E.counitIso.hom.app (Rₙ.obj M))
    (heL : ∀ M, b.unit.app M ≫ Rₙ.map (eL.hom.app M) =
      (((E.symm.toAdjunction.comp a).comp F.toAdjunction).ofNatIsoRight eR.symm).unit.app M)
    (M : A) :
    E.inverse.map (b.unit.app M) ≫ q.hom.app (Lₙ.obj M) ≫
      R.map ((inverseValuedIso E F eL).hom.app M) = a.unit.app (E.inverse.obj M) := by
  have h := congrArg ((E).inverse.map)
    (heL M)
  have hn := (q).hom.naturality
    ((eL).hom.app M)
  simp only [Functor.comp_map] at hn
  have ht := transportUnit_comparison E F a Rₙ q eR heR M
  have hh := congrArg (fun a => a ≫ (q).hom.app
    ((((E).inverse ⋙ L) ⋙
      (F).functor).obj M)) h
  rw [Functor.map_comp, Category.assoc, hn, ht] at hh
  have hc := congrArg (fun a => a ≫ (R).map
    ((F).unitIso.inv.app
      ((L).obj ((E).inverse.obj M)))) hh
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    ] at hc
  erw [(R).map_id] at hc
  have hc' := hc.trans (Category.comp_id _)
  simpa only [inverseValuedIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.rightUnitor_hom_app, Iso.symm_hom, Functor.map_comp, Functor.map_id,
    Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id,
    Category.assoc] using hc'

end Units

section Exchange

variable {C D V E : Type*} [Category* C] [Category* D] [Category* V] [Category* E]
  (W : D ⥤ E) {F G : C ⥤ D} {U : C ⥤ V} {P Q : V ⥤ E}

/-- The original valued exchange between the two fixed comparison endpoints. -/
def exchangeComparisonIso (s : F ⋙ W ≅ U ⋙ P) (t : G ⋙ W ≅ U ⋙ Q) (e : P ≅ Q) :
    F ⋙ W ≅ G ⋙ W :=
  s ≪≫ Functor.isoWhiskerLeft U e ≪≫ t.symm

/-- The original whole whiskered value gives the comparison square before evaluation. -/
theorem hom_comparison_of_whisker (c : F ≅ G)
    (s : F ⋙ W ≅ U ⋙ P) (t : G ⋙ W ≅ U ⋙ Q) (e : P ≅ Q)
    (hc : Functor.isoWhiskerRight c W = exchangeComparisonIso W s t e) :
    Functor.whiskerRight c.hom W ≫ t.hom = s.hom ≫ Functor.whiskerLeft U e.hom := by
  have h := congrArg (fun z => z ≫ t.hom) (congrArg Iso.hom hc)
  simpa only [exchangeComparisonIso, Functor.isoWhiskerRight_hom, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerLeft_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using h

variable [W.Full] [W.Faithful]

/-- The genuine exchange is the preimage of its original valued comparison. -/
def exchangeIso (s : F ⋙ W ≅ U ⋙ P) (t : G ⋙ W ≅ U ⋙ Q) (e : P ≅ Q) : F ≅ G :=
  ((Functor.whiskeringRight C D E).obj W).preimageIso (exchangeComparisonIso W s t e)

/-- Whole value of the actual preimage exchange through the same fully faithful functor. -/
theorem exchangeIso_whisker (s : F ⋙ W ≅ U ⋙ P) (t : G ⋙ W ≅ U ⋙ Q) (e : P ≅ Q) :
    Functor.isoWhiskerRight (exchangeIso W s t e) W = exchangeComparisonIso W s t e := by
  apply Iso.ext
  exact ((Functor.whiskeringRight C D E).obj W).map_preimage _

/-- The actual exchanged transformation satisfies its original whole comparison square. -/
theorem exchangeIso_hom_comparison
    (s : F ⋙ W ≅ U ⋙ P) (t : G ⋙ W ≅ U ⋙ Q) (e : P ≅ Q) :
    Functor.whiskerRight (exchangeIso W s t e).hom W ≫ t.hom =
      s.hom ≫ Functor.whiskerLeft U e.hom :=
  hom_comparison_of_whisker W (exchangeIso W s t e) s t e (exchangeIso_whisker W s t e)

end Exchange

section Values

variable {C D : Type*} [Category* C] [Category* D]

/-- Inverting the original comparison square preserves its specified endpoint maps. -/
theorem inverse_comparison (Q : C ⥤ D) {X Y : C} {U V : D}
    (a : X ≅ Y) (v : U ≅ V) (s : Q.obj X ⟶ U) (t : Q.obj Y ⟶ V)
    (h : Q.map a.hom ≫ t = s ≫ v.hom) :
    Q.map a.inv ≫ s = t ≫ v.inv := by
  apply (Iso.inv_comp_eq (Q.mapIso a)).2
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv v).2
  exact h.symm

/-- The original three-factor square is transported through its two composition comparisons. -/
theorem comparison_square (Q : C ⥤ D)
    {X₀ X₁ Y₀ Y₁ : C} {U₀ U₁ V₀ V₁ : D}
    (a : X₀ ≅ Y₀) (b : X₁ ≅ Y₁) (v₀ : U₀ ≅ V₀) (v₁ : U₁ ≅ V₁)
    (c₀ : Q.obj X₀ ⟶ U₀) (c₁ : Q.obj X₁ ⟶ U₁)
    (d₀ : Q.obj Y₀ ⟶ V₀) (d₁ : Q.obj Y₁ ⟶ V₁)
    (t : X₀ ⟶ X₁) (s : U₀ ⟶ U₁)
    (ha : Q.map a.inv ≫ c₀ = d₀ ≫ v₀.inv)
    (hb : Q.map b.hom ≫ d₁ = c₁ ≫ v₁.hom)
    (ht : Q.map t ≫ c₁ = c₀ ≫ s) :
    Q.map (a.inv ≫ t ≫ b.hom) ≫ d₁ = d₀ ≫ v₀.inv ≫ s ≫ v₁.hom := by
  simp only [Functor.map_comp, Category.assoc]
  rw [hb, ← Category.assoc (Q.map t) c₁, ht]
  simp only [Category.assoc]
  rw [← Category.assoc (Q.map a.inv) c₀, ha]
  simp only [Category.assoc]

/-- Original square aliases keep their actual maps through the whole comparison argument. -/
theorem comparison_square_of_aliases (Q : C ⥤ D)
    {X₀ X₁ Y₀ Y₁ : C} {U₀ U₁ V₀ V₁ : D}
    (a : X₀ ≅ Y₀) (b : X₁ ≅ Y₁) (v₀ : U₀ ≅ V₀) (v₁ : U₁ ≅ V₁)
    (c₀ : Q.obj X₀ ⟶ U₀) (c₁ : Q.obj X₁ ⟶ U₁)
    (d₀ : Q.obj Y₀ ⟶ V₀) (d₁ : Q.obj Y₁ ⟶ V₁)
    (t : X₀ ⟶ X₁) (s : U₀ ⟶ U₁) (p : Y₀ ≅ Y₁) (q : V₀ ≅ V₁)
    (hp : p.hom = a.inv ≫ t ≫ b.hom) (hq : q.hom = v₀.inv ≫ s ≫ v₁.hom)
    (ha : Q.map a.inv ≫ c₀ = d₀ ≫ v₀.inv)
    (hb : Q.map b.hom ≫ d₁ = c₁ ≫ v₁.hom)
    (ht : Q.map t ≫ c₁ = c₀ ≫ s) :
    Q.map p.hom ≫ d₁ = d₀ ≫ q.hom := by
  rw [hp, hq]
  exact comparison_square Q a b v₀ v₁ c₀ c₁ d₀ d₁ t s ha hb ht

end Values

/-- Equality transport in the original comparison family is a whole natural square. -/
theorem comparison_eqToIso
    {I : Sort*} {C D C' D' : Type*}
    [Category* C] [Category* D] [Category* C'] [Category* D']
    (P : I → C ⥤ D) (P' : I → C' ⥤ D') (U : C ⥤ C') (V : D ⥤ D')
    (c : ∀ i, P i ⋙ V ≅ U ⋙ P' i) {i j : I} (h : i = j) :
    Functor.whiskerRight (eqToIso (congrArg P h)).hom V ≫ (c j).hom =
      (c i).hom ≫ Functor.whiskerLeft U (eqToIso (congrArg P' h)).hom := by
  subst j
  simp

/-- The original inverse-first three-factor isomorphism retains its component value. -/
theorem inverse_iso_chain_app
    {C D : Type*} [Category* C] [Category* D]
    {F₀ F₁ F₂ F₃ : C ⥤ D} (a : F₁ ≅ F₀) (b : F₁ ≅ F₂)
    (c : F₂ ≅ F₃) (M : C) :
    (a.symm ≪≫ b ≪≫ c).hom.app M = a.inv.app M ≫ b.hom.app M ≫ c.hom.app M := rfl

end CategoryTheory.ValuedComparison
