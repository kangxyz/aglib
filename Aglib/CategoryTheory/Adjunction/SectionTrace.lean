/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.Whole
public import Aglib.CategoryTheory.Adjunction.OpenRefinementNormalization
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Shift.ShiftedHom

/-! Original coefficient and trace comparison values retained before specialization. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The original coefficient section equation, before its data are specialized. -/
def SectionCoefficientValue {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) (G : B ⥤ A) {H : A ⥤ A} (c : H ≅ F ⋙ G) (i : H ≅ 𝟭 A)
    {M : A} {N : B} (a : F.obj M ≅ N) (b : G.obj N ≅ M) : Prop :=
  c.hom.app M ≫ G.map a.hom ≫ b.hom = i.hom.app M

end CategoryTheory

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

/-- The original horizontal identity comparison at the original object. -/
def HorizontalIdentityValue (R : C ⥤ D) {G : D ⥤ D} {H : C ⥤ C}
    (β : R ⋙ G ⟶ H ⋙ R) (dH : H ≅ 𝟭 C) (dG : G ≅ 𝟭 D) (K : C) : Prop :=
  β.app K ≫ R.map (dH.hom.app K) = dG.hom.app (R.obj K)

/-- Consume the original whole identity square before evaluating its mate. -/
theorem HorizontalIdentityValue.of_mate {L : D ⥤ C} {R : C ⥤ D}
    {G : D ⥤ D} {H : C ⥤ C} (adj : L ⊣ R)
    (α : G ⋙ L ≅ L ⋙ H) (dG : G ≅ 𝟭 D) (dH : H ≅ 𝟭 C)
    (β : R ⋙ G ⟶ H ⋙ R)
    (hβ : β = (mateEquiv adj adj (TwoSquare.mk G L L H α.hom)).natTrans)
    (h : α ≪≫ Functor.isoWhiskerLeft L dH ≪≫ Functor.rightUnitor L =
      Functor.isoWhiskerRight dG L ≪≫ Functor.leftUnitor L) (K : C) :
    HorizontalIdentityValue R β dH dG K :=
  originalMate_horizontal_identity adj α dG dH β hβ h K

/-- Equality transport of original indexed comparison data is performed before specialization. -/
theorem HorizontalIdentityValue.transport_index
    (R : C ⥤ D) {A B : Type*} (P : A → C ⥤ C) (Q : B → D ⥤ D)
    (W : B → A → Prop) (β : ∀ b a, W b a → (R ⋙ Q b ⟶ P a ⋙ R))
    (a₀ : A) (b₀ : B) (dP : P a₀ ≅ 𝟭 C) (dQ : Q b₀ ≅ 𝟭 D) (K : C)
    (h₀ : ∀ h : W b₀ a₀, HorizontalIdentityValue R (β b₀ a₀ h) dP dQ K)
    (a : A) (b : B) (ha : a = a₀) (hb : b = b₀) (h : W b a) :
    HorizontalIdentityValue R (β b a h)
      (eqToIso (congrArg P ha) ≪≫ dP) (eqToIso (congrArg Q hb) ≪≫ dQ) K := by
  subst a
  subst b
  simpa only [eqToIso_refl, Iso.refl_trans] using h₀ h

end CategoryTheory

namespace CategoryTheory

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {R₀ : B ⥤ A} {R₁ : D ⥤ C} {G₁ : A ⥤ C} {G₂ : C ⥤ A}
  {H₁ : B ⥤ D} {H₂ : D ⥤ B} {G₀ : A ⥤ A} {H₀ : B ⥤ B}

/-- Original coefficient transport completes the original horizontal exchange loop. -/
theorem actualHorizontalMateEquation_coefficient_loop
    (β₁ : R₀ ⋙ G₁ ⟶ H₁ ⋙ R₁) (β₂ : R₁ ⋙ G₂ ⟶ H₂ ⋙ R₀)
    (β₀ : R₀ ⋙ G₀ ⟶ H₀ ⋙ R₀)
    (γ : G₀ ≅ G₁ ⋙ G₂) (δ : H₀ ≅ H₁ ⋙ H₂)
    (eG : G₀ ≅ 𝟭 A) (eH : H₀ ≅ 𝟭 B)
    (K : B) (L : D) (a : H₁.obj K ≅ L) (b : H₂.obj L ≅ K)
    (hp : ActualHorizontalMateEquation β₁ β₂ β₀ γ.hom δ.hom K)
    (hi : HorizontalIdentityValue R₀ β₀ eH eG K)
    (hc : δ.hom.app K ≫ H₂.map a.hom ≫ b.hom = eH.hom.app K) :
    γ.hom.app (R₀.obj K) ≫ G₂.map (β₁.app K ≫ R₁.map a.hom) ≫
      (β₂.app L ≫ R₀.map b.hom) = eG.hom.app (R₀.obj K) := by
  have hn := β₂.naturality a.hom
  change G₂.map (R₁.map a.hom) ≫ β₂.app L =
    β₂.app (H₁.obj K) ≫ R₀.map (H₂.map a.hom) at hn
  have h := actualHorizontalMateEquation_eq β₁ β₂ β₀ γ.hom δ.hom K hp
  dsimp only [HorizontalIdentityValue] at hi
  simp only [G₂.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% h]
  simp only [← R₀.map_comp]
  rw [hc]
  exact hi

end CategoryTheory

namespace CategoryTheory

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {R₀ : B ⥤ A} {R₁ : D ⥤ C} {G₁ : A ⥤ C} {G₂ : C ⥤ A}
  {H₁ : B ⥤ D} {H₂ : D ⥤ B} {G₀ : A ⥤ A} {H₀ : B ⥤ B}

/-- The corrected proper exchange and its original rational restriction form one loop. -/
def CorrectedExchangeLoop
    (β₁ : R₀ ⋙ G₁ ⟶ H₁ ⋙ R₁) (β₂ : R₁ ⋙ G₂ ⟶ H₂ ⋙ R₀)
    (γ : G₀ ≅ G₁ ⋙ G₂) (eG : G₀ ≅ 𝟭 A)
    (K : B) (L : D) (a : H₁.obj K ≅ L) (b : H₂.obj L ≅ K) : Prop :=
  γ.hom.app (R₀.obj K) ≫ G₂.map (β₁.app K ≫ R₁.map a.hom) ≫
    (β₂.app L ≫ R₀.map b.hom) = eG.hom.app (R₀.obj K)

/-- Keep both actual section predicates folded while composing the exchange equation. -/
theorem CorrectedExchangeLoop.of_original_values
    (β₁ : R₀ ⋙ G₁ ⟶ H₁ ⋙ R₁) (β₂ : R₁ ⋙ G₂ ⟶ H₂ ⋙ R₀)
    (β₀ : R₀ ⋙ G₀ ⟶ H₀ ⋙ R₀)
    (γ : G₀ ≅ G₁ ⋙ G₂) (δ : H₀ ≅ H₁ ⋙ H₂)
    (eG : G₀ ≅ 𝟭 A) (eH : H₀ ≅ 𝟭 B)
    (K : B) (L : D) (a : H₁.obj K ≅ L) (b : H₂.obj L ≅ K)
    (hp : ActualHorizontalMateEquation β₁ β₂ β₀ γ.hom δ.hom K)
    (hi : HorizontalIdentityValue R₀ β₀ eH eG K)
    (hc : SectionCoefficientValue H₁ H₂ δ eH a b) :
    CorrectedExchangeLoop β₁ β₂ γ eG K L a b :=
  actualHorizontalMateEquation_coefficient_loop β₁ β₂ β₀ γ δ eG eH K L a b hp hi hc

end CategoryTheory

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

/-- The same transported trace has the original comparison as its exact pullback. -/
theorem transported_trace_pullback
    (F : C ⥤ D) (G : D ⥤ C) (η : F ⋙ G ≅ 𝟭 C)
    {I K : C} {J L : D} (u : F.obj I ≅ J) (v : G.obj J ≅ I)
    (e : F.obj K ≅ L) (k : G.obj L ⟶ K) (a : K ⟶ I)
    (hK : G.map e.hom ≫ k = η.hom.app K)
    (hI : G.map u.hom ≫ v.hom = η.hom.app I) :
    G.map (e.inv ≫ F.map a ≫ u.hom) ≫ v.hom = k ≫ a := by
  have he : G.map e.inv ≫ η.hom.app K = k := by
    rw [← hK, ← G.map_comp_assoc, e.inv_hom_id, G.map_id, Category.id_comp]
  have hn := η.hom.naturality a
  change G.map (F.map a) ≫ η.hom.app I = η.hom.app K ≫ a at hn
  simp only [G.map_comp, Category.assoc]
  rw [hI, hn, ← Category.assoc, he]


end CategoryTheory

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]

/-- The same original exchange loop commutes with the installed shifts. -/
theorem transported_loop_shift
    (F : C ⥤ D) (G : D ⥤ C) [F.CommShift ℤ] [G.CommShift ℤ]
    (η : F ⋙ G ≅ 𝟭 C) [NatTrans.CommShift η.hom ℤ]
    {K : C} {L : D} (e : F.obj K ≅ L) (k : G.obj L ⟶ K)
    (h : G.map e.hom ≫ k = η.hom.app K) (q : ℤ) :
    let E := (F.commShiftIso q).app K ≪≫ (shiftFunctor D q).mapIso e
    G.map E.hom ≫ (G.commShiftIso q).hom.app L ≫ k⟦q⟧' = η.hom.app (K⟦q⟧) := by
  dsimp only
  have hn := G.commShiftIso_hom_naturality e.hom q
  have hs := NatTrans.shift_app_comm η.hom q K
  simp only [Functor.commShiftIso_id_hom_app] at hs
  have hm : (G.map e.hom)⟦q⟧' ≫ k⟦q⟧' = (η.hom.app K)⟦q⟧' := by
    rw [← (shiftFunctor C q).map_comp, h]
  change G.map ((F.commShiftIso q).hom.app K ≫ e.hom⟦q⟧') ≫
    (G.commShiftIso q).hom.app L ≫ k⟦q⟧' = _
  rw [G.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn, hm]
  rw [← Category.assoc, ← Functor.commShiftIso_comp_hom_app]
  exact hs.trans (Category.comp_id (η.hom.app (K⟦q⟧)))

end CategoryTheory
