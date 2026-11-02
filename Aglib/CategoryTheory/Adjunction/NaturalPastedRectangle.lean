/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.PastedRectangleNormalization
public import
  Aglib.CategoryTheory.Adjunction.Mates.Whole

/-! # Original pasted rectangles with whole functor-level boundaries

Both input route equations and the normalized output keep regular proposition
heads. Evaluation at objects and cancellation happen only in abstract categories.
-/

@[expose] public section

namespace CategoryTheory

section Vertical
variable {A B C D E F : Type*}
  [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
  {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
  {R₁ : B ⥤ A} {R₂ : E ⥤ D} {R₃ : C ⥤ B} {R₄ : F ⥤ E}
  {R₀ : C ⥤ A} {R₀' : F ⥤ D}

/-- Whole family of the original vertical route equations. -/
def ActualVerticalMatePasting
    (β₁ : R₁ ⋙ G ⟶ H ⋙ R₂) (β₂ : R₃ ⋙ H ⟶ K ⋙ R₄)
    (β : R₀ ⋙ G ⟶ K ⋙ R₀') (d₁ : R₀ ⟶ R₃ ⋙ R₁) (d₂ : R₀' ⟶ R₄ ⋙ R₂) : Prop :=
  ∀ M, ActualVerticalMateEquation β₁ β₂ β d₁ d₂ M

/-- Keep the identified original maps opaque while importing proved native mate pasting. -/
theorem actualVerticalMatePasting_of_mates
    {L₁ : A ⥤ B} {L₂ : D ⥤ E} {L₃ : B ⥤ C} {L₄ : E ⥤ F}
    {L₀ : A ⥤ C} {L₀' : D ⥤ F}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    (a₀ : L₀ ⊣ R₀) (a₀' : L₀' ⊣ R₀')
    (α₁ : TwoSquare G L₁ L₂ H) (α₂ : TwoSquare H L₃ L₄ K)
    (α : TwoSquare G L₀ L₀' K) (d₁ : R₀ ≅ R₃ ⋙ R₁) (d₂ : R₀' ≅ R₄ ⋙ R₂)
    (β₁ : R₁ ⋙ G ⟶ H ⋙ R₂) (β₂ : R₃ ⋙ H ⟶ K ⋙ R₄)
    (β : R₀ ⋙ G ⟶ K ⋙ R₀')
    (hβ₁ : β₁ = (mateEquiv a₁ a₂ α₁).natTrans)
    (hβ₂ : β₂ = (mateEquiv a₃ a₄ α₂).natTrans)
    (hβ : β = (mateEquiv a₀ a₀' α).natTrans)
    (h : ∀ M, VerticalMateEquation α₁ α₂ α d₁ d₂ a₁ a₂ a₃ a₄ a₀ a₀' M) :
    ActualVerticalMatePasting β₁ β₂ β d₁.hom d₂.hom := by
  intro M
  exact actualVerticalMateEquation_of_mates a₁ a₂ a₃ a₄ a₀ a₀'
    α₁ α₂ α d₁ d₂ β₁ β₂ β hβ₁ hβ₂ hβ M (h M)

end Vertical

/-- Whole equality transport around a triangle of original functors. -/
theorem eqToIso_triangle {C D : Type*} [Category C] [Category D]
    {F G H : C ⥤ D} (e : F = H) (f : G = H) (g : F = G) :
    (eqToIso e).inv ≫ (eqToIso g).hom = (eqToIso f).inv := by
  subst G
  subst H
  simp

section Rectangle

variable {A B C D E F G : Type*}
  [Category A] [Category B] [Category C] [Category D] [Category E] [Category F] [Category G]
  {HA : A ⥤ B} {QC : A ⥤ C} {QD : B ⥤ C}
  {HB : D ⥤ E} {RC : D ⥤ F} {RD : E ⥤ G} {HT : F ⥤ G}
  {IC : C ⥤ F} {ID : C ⥤ G} {MC : A ⥤ D} {MD : B ⥤ E} {T : C ⥤ C}

/-- Whole normalized rectangle, retaining original functors, transformations
and source/target comparisons before evaluation at a coefficient. -/
def NaturalPastedRectangleEquation
    (σD : QD ⋙ ID ⟶ MD ⋙ RD) (σMid : HA ⋙ MD ⟶ MC ⋙ HB)
    (σTarget : T ⋙ ID ⟶ IC ⋙ HT) (σC : QC ⋙ IC ⟶ MC ⋙ RC)
    (over : HA ⋙ QD ≅ QC) (rid : T ≅ 𝟭 C) (comm : RC ⋙ HT ≅ HB ⋙ RD) : Prop :=
  ∀ K, PastedRectangleEquation
    (ID.map (over.inv.app K)) (ID.map (rid.inv.app (QC.obj K)))
    (σD.app (HA.obj K) ≫ RD.map (σMid.app K))
    (σTarget.app (QC.obj K) ≫ HT.map (σC.app K)) (comm.hom.app (MC.obj K))

/-- Normalize two proved original route families and their whole equality square.
All component conversions occur here, with categories and maps still abstract. -/
theorem naturalPastedRectangle_of_vertical
    {G₁ G₂ : A ⥤ C} {F₁ F₂ : D ⥤ G}
    (σD : QD ⋙ ID ⟶ MD ⋙ RD) (σMid : HA ⋙ MD ⟶ MC ⋙ HB)
    (σTarget : T ⋙ ID ⟶ IC ⋙ HT) (σC : QC ⋙ IC ⟶ MC ⋙ RC)
    (s₁ : G₁ ⋙ ID ⟶ MC ⋙ F₁) (s₂ : G₂ ⋙ ID ⟶ MC ⋙ F₂)
    (c₁ : G₁ ≅ HA ⋙ QD) (c₂ : G₂ ≅ QC ⋙ T)
    (d₁ : F₁ ≅ HB ⋙ RD) (d₂ : F₂ ≅ RC ⋙ HT)
    (e₁ : G₁ ≅ QC) (e₂ : G₂ ≅ QC) (eS : G₁ ≅ G₂) (eT : F₁ ≅ F₂)
    (over : HA ⋙ QD ≅ QC) (rid : T ≅ 𝟭 C) (comm : RC ⋙ HT ≅ HB ⋙ RD)
    (h₁ : ActualVerticalMatePasting σD σMid s₁ c₁.hom d₁.hom)
    (h₂ : ActualVerticalMatePasting σTarget σC s₂ c₂.hom d₂.hom)
    (hS : e₁.inv ≫ eS.hom = e₂.inv)
    (hT : s₁ ≫ Functor.whiskerLeft MC eT.hom = Functor.whiskerRight eS.hom ID ≫ s₂)
    (hOver : over = c₁.symm ≪≫ e₁)
    (hId : c₂ ≪≫ Functor.isoWhiskerLeft QC rid ≪≫ Functor.rightUnitor QC = e₂)
    (hComm : d₂.symm ≪≫ eT.symm ≪≫ d₁ = comm) :
    NaturalPastedRectangleEquation σD σMid σTarget σC over rid comm := by
  intro K
  have hSK : ID.map (e₁.inv.app K) ≫ (ID.mapIso (eS.app K)).hom =
      ID.map (e₂.inv.app K) := by
    exact (ID.map_comp _ _).symm.trans
      (congrArg ID.map (congrArg (fun t => t.app K) hS))
  have hTK : s₁.app K ≫ (eT.app (MC.obj K)).hom =
      (ID.mapIso (eS.app K)).hom ≫ s₂.app K := congrArg (fun t => t.app K) hT
  have hu : ID.map (e₁.inv.app K) ≫ (ID.mapIso (c₁.app K)).hom =
      ID.map (over.inv.app K) := by
    rw [hOver]
    exact (ID.map_comp _ _).symm
  have hi := iso_inv_comp_of_comp_eq c₂
    (Functor.isoWhiskerLeft QC rid ≪≫ Functor.rightUnitor QC) e₂
    (by simpa only [Iso.trans_assoc] using hId)
  have hiK := congrArg (fun e => e.hom.app K) hi
  change e₂.inv.app K ≫ c₂.hom.app K = 𝟙 _ ≫ rid.inv.app (QC.obj K) at hiK
  have hv : ID.map (e₂.inv.app K) ≫ (ID.mapIso (c₂.app K)).hom =
      ID.map (rid.inv.app (QC.obj K)) :=
    (ID.map_comp _ _).symm.trans (congrArg ID.map (hiK.trans (Category.id_comp _)))
  have hc : (d₂.app (MC.obj K)).inv ≫ (eT.app (MC.obj K)).inv ≫
      (d₁.app (MC.obj K)).hom = comm.hom.app (MC.obj K) :=
    congrArg (fun e => e.hom.app (MC.obj K)) hComm
  exact pastedRectangle_normalize_eq
    (ID.map (e₁.inv.app K)) (ID.map (e₂.inv.app K))
    (ID.mapIso (c₁.app K)) (ID.mapIso (c₂.app K))
    (s₁.app K) (s₂.app K) (d₁.app (MC.obj K)) (d₂.app (MC.obj K))
    (σD.app (HA.obj K) ≫ RD.map (σMid.app K))
    (σTarget.app (QC.obj K) ≫ HT.map (σC.app K))
    (ID.mapIso (eS.app K)) (eT.app (MC.obj K)) (h₁ K) (h₂ K) hSK hTK
    _ _ _ hu hv hc

end Rectangle

end CategoryTheory
