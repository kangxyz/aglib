/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Aglib.CategoryTheory.Adjunction.LeftAdjointComparison

/-! # Coherence of the original selected adjoint comparisons

The specified comparisons are identified with the native adjoint-comparison
constructors by their actual conjugates. Existing associativity and unit laws
then apply. Equality transport is confined to the two spellings of the same
actual total composite; no extra realization or coherence premise is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.SelectedAdjointCoherence

/-- The specified left composition comparison is the native canonical one. -/
theorem leftComp_eq_symm
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L : A ⥤ C} {R : C ⥤ A}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a : L ⊣ R)
    (c : L ≅ L₁ ⋙ L₂) (d : R₂ ⋙ R₁ ≅ R)
    (hc : conjugateEquiv (a₁.comp a₂) a c.hom = d.hom) :
    Adjunction.leftAdjointCompIso a₁ a₂ a d = c.symm := by
  apply Iso.ext_inv
  apply (conjugateEquiv (a₁.comp a₂) a).injective
  exact (Adjunction.conjugateEquiv_leftAdjointCompIso_inv a₁ a₂ a d).trans hc.symm

/-- The specified left identity comparison is fixed by its original conjugate. -/
theorem leftId_eq
    {A : Type*} [Category* A] {L R : A ⥤ A}
    (a : L ⊣ R) (c : L ≅ 𝟭 A) (d : R ≅ 𝟭 A)
    (hc : conjugateEquiv Adjunction.id a c.hom = d.inv) :
    Adjunction.leftAdjointIdIso a d = c := by
  apply Iso.ext
  apply (conjugateEquiv Adjunction.id a).injective
  exact (Adjunction.conjugateEquiv_leftAdjointIdIso_hom a d).trans hc.symm

/-- Canonical left comparison respects the original equality of its total index. -/
theorem leftComp_transport
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    {I : Sort*} (L : I → A ⥤ C) (R : I → C ⥤ A) (a : ∀ i, L i ⊣ R i)
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) {i j : I} (h : i = j)
    (d : R₂ ⋙ R₁ ≅ R i) :
    Adjunction.leftAdjointCompIso a₁ a₂ (a i) d ≪≫ eqToIso (congrArg L h) =
      Adjunction.leftAdjointCompIso a₁ a₂ (a j) (d ≪≫ eqToIso (congrArg R h)) := by
  subst j
  simp

/-- The inverse equality transport retains the same native comparison choice. -/
theorem leftComp_transport_inv
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    {I : Sort*} (L : I → A ⥤ C) (R : I → C ⥤ A) (a : ∀ i, L i ⊣ R i)
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) {i j : I} (h : i = j)
    (d : R₂ ⋙ R₁ ≅ R j) :
    Adjunction.leftAdjointCompIso a₁ a₂ (a i)
        (d ≪≫ (eqToIso (congrArg R h)).symm) =
      Adjunction.leftAdjointCompIso a₁ a₂ (a j) d ≪≫
        (eqToIso (congrArg L h)).symm := by
  subst j
  simp

/-- The original right component law yields the original left associativity,
using the native whole associativity theorem and exact index transport. -/
theorem assoc_of_right_app
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {I : Sort*} (L : I → A ⥤ D) (R : I → D ⥤ A) (a : ∀ i, L i ⊣ R i)
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L₃ : C ⥤ D} {R₃ : D ⥤ C} {L₁₂ : A ⥤ C} {R₁₂ : C ⥤ A}
    {L₂₃ : B ⥤ D} {R₂₃ : D ⥤ B}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (a₁₂ : L₁₂ ⊣ R₁₂) (a₂₃ : L₂₃ ⊣ R₂₃) {i j : I} (h : i = j)
    (c₁₂ : L₁₂ ≅ L₁ ⋙ L₂) (c₂₃ : L₂₃ ≅ L₂ ⋙ L₃)
    (c₁ : L i ≅ L₁ ⋙ L₂₃) (c₂ : L j ≅ L₁₂ ⋙ L₃)
    (d₁₂ : R₂ ⋙ R₁ ≅ R₁₂) (d₂₃ : R₃ ⋙ R₂ ≅ R₂₃)
    (d₁ : R₂₃ ⋙ R₁ ≅ R i) (d₂ : R₃ ⋙ R₁₂ ≅ R j)
    (hc₁₂ : conjugateEquiv (a₁.comp a₂) a₁₂ c₁₂.hom = d₁₂.hom)
    (hc₂₃ : conjugateEquiv (a₂.comp a₃) a₂₃ c₂₃.hom = d₂₃.hom)
    (hc₁ : conjugateEquiv (a₁.comp a₂₃) (a i) c₁.hom = d₁.hom)
    (hc₂ : conjugateEquiv (a₁₂.comp a₃) (a j) c₂.hom = d₂.hom)
    (hd : ∀ X, R₁.map (d₂₃.hom.app X) ≫ d₁.hom.app X ≫
        (eqToIso (congrArg R h)).hom.app X =
      d₁₂.hom.app (R₃.obj X) ≫ d₂.hom.app X) :
    c₁ ≪≫ Functor.isoWhiskerLeft L₁ c₂₃ =
      eqToIso (congrArg L h) ≪≫ c₂ ≪≫
        Functor.isoWhiskerRight c₁₂ L₃ ≪≫ Functor.associator L₁ L₂ L₃ := by
  let e := d₂ ≪≫ (eqToIso (congrArg R h)).symm
  have hright : Functor.isoWhiskerLeft R₃ d₁₂ ≪≫ e =
      (Functor.associator R₃ R₂ R₁).symm ≪≫
        Functor.isoWhiskerRight d₂₃ R₁ ≪≫ d₁ := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    have hh := congrArg (fun k => k ≫ (eqToIso (congrArg R h)).inv.app X) (hd X)
    simpa only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Category.id_comp, Category.assoc,
      Iso.hom_inv_id_app, Category.comp_id] using hh.symm
  have hm := Adjunction.leftAdjointCompIso_assoc a₁ a₂ a₃ a₁₂ a₂₃ (a i)
    d₁₂ d₂₃ d₁ e hright
  rw [leftComp_eq_symm a₁ a₂ a₁₂ c₁₂ d₁₂ hc₁₂,
    leftComp_eq_symm a₂ a₃ a₂₃ c₂₃ d₂₃ hc₂₃,
    leftComp_eq_symm a₁ a₂₃ (a i) c₁ d₁ hc₁] at hm
  have hlast : Adjunction.leftAdjointCompIso a₁₂ a₃ (a i) e =
      c₂.symm ≪≫ (eqToIso (congrArg L h)).symm := by
    rw [show e = d₂ ≪≫ (eqToIso (congrArg R h)).symm from rfl,
      leftComp_transport_inv L R a a₁₂ a₃ h d₂,
      leftComp_eq_symm a₁₂ a₃ (a j) c₂ d₂ hc₂]
  rw [hlast] at hm
  apply Iso.ext
  simpa only [Iso.trans_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Category.assoc] using congrArg Iso.inv hm

/-- The source-identity law retains its actual total-index equality transport. -/
theorem comp_id_of_right
    {A B : Type*} [Category* A] [Category* B]
    {I : Sort*} (L : I → A ⥤ B) (R : I → B ⥤ A) (a : ∀ i, L i ⊣ R i)
    {J K : B ⥤ B} (ai : J ⊣ K) {i j : I} (h : i = j)
    (c : L i ≅ L j ⋙ J) (d : K ⋙ R j ≅ R i)
    (ci : J ≅ 𝟭 B) (di : K ≅ 𝟭 B)
    (hc : conjugateEquiv ((a j).comp ai) (a i) c.hom = d.hom)
    (hi : conjugateEquiv Adjunction.id ai ci.hom = di.inv)
    (hd : d.symm ≪≫ Functor.isoWhiskerRight di (R j) ≪≫
      Functor.leftUnitor (R j) = eqToIso (congrArg R h)) :
    c ≪≫ Functor.isoWhiskerLeft (L j) ci ≪≫ Functor.rightUnitor (L j) =
      eqToIso (congrArg L h) := by
  have hr : d ≪≫ eqToIso (congrArg R h) =
      Functor.isoWhiskerRight di (R j) ≪≫ Functor.leftUnitor (R j) := by
    rw [← hd]
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  have hm := Adjunction.leftAdjointCompIso_comp_id (a j) ai
    (d ≪≫ eqToIso (congrArg R h)) di hr
  rw [← leftComp_transport L R a (a j) ai h d,
    leftComp_eq_symm (a j) ai (a i) c d hc, leftId_eq ai ci di hi] at hm
  apply Iso.ext
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc] using
    (congrArg (fun e : L j ⋙ J ≅ L j => c.hom ≫ e.hom) hm).symm

/-- The target-identity law retains its actual total-index equality transport. -/
theorem id_comp_of_right
    {A B : Type*} [Category* A] [Category* B]
    {I : Sort*} (L : I → A ⥤ B) (R : I → B ⥤ A) (a : ∀ i, L i ⊣ R i)
    {J K : A ⥤ A} (ai : J ⊣ K) {i j : I} (h : i = j)
    (c : L i ≅ J ⋙ L j) (d : R j ⋙ K ≅ R i)
    (ci : J ≅ 𝟭 A) (di : K ≅ 𝟭 A)
    (hc : conjugateEquiv (ai.comp (a j)) (a i) c.hom = d.hom)
    (hi : conjugateEquiv Adjunction.id ai ci.hom = di.inv)
    (hd : d.symm ≪≫ Functor.isoWhiskerLeft (R j) di ≪≫
      Functor.rightUnitor (R j) = eqToIso (congrArg R h)) :
    c ≪≫ Functor.isoWhiskerRight ci (L j) ≪≫ Functor.leftUnitor (L j) =
      eqToIso (congrArg L h) := by
  have hr : d ≪≫ eqToIso (congrArg R h) =
      Functor.isoWhiskerLeft (R j) di ≪≫ Functor.rightUnitor (R j) := by
    rw [← hd]
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  have hm := Adjunction.leftAdjointCompIso_id_comp ai (a j)
    (d ≪≫ eqToIso (congrArg R h)) di hr
  rw [← leftComp_transport L R a ai (a j) h d,
    leftComp_eq_symm ai (a j) (a i) c d hc, leftId_eq ai ci di hi] at hm
  apply Iso.ext
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc] using
    (congrArg (fun e : J ⋙ L j ≅ L j => c.hom ≫ e.hom) hm).symm

end CategoryTheory.SelectedAdjointCoherence
