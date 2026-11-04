/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Shift.AdjunctionTransport

/-! Original shifted and regraded adjunct values. -/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory


section UnitValue

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {U : A ⥤ C} {V : B ⥤ D}

/-- The original unit adjunct equation used by the shifted exchange. -/
def UnitAdjunctValue (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (d : R₁ ⋙ U ⟶ V ⋙ R₂)
    {I : A} {J : B} {I' : C} {J' : D}
    (e : L₁.obj I ≅ J) (e' : L₂.obj I' ≅ J') (u : U.obj I ≅ I') (v : V.obj J ≅ J') : Prop :=
  u.inv ≫ U.map (adj₁.homEquiv I J e.hom) ≫ d.app J ≫ R₂.map v.hom =
    adj₂.homEquiv I' J' e'.hom

/-- Read the original unit equation without changing its maps. -/
theorem UnitAdjunctValue.eq (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (d : R₁ ⋙ U ⟶ V ⋙ R₂)
    {I : A} {J : B} {I' : C} {J' : D}
    {e : L₁.obj I ≅ J} {e' : L₂.obj I' ≅ J'} {u : U.obj I ≅ I'} {v : V.obj J ≅ J'}
    (h : UnitAdjunctValue adj₁ adj₂ d e e' u v) :
    u.inv ≫ U.map (adj₁.homEquiv I J e.hom) ≫ d.app J ≫ R₂.map v.hom =
      adj₂.homEquiv I' J' e'.hom := h

end UnitValue
/-- The original component obtained by the specified source and target transports. -/
def TransportedComponentValue
    {A C : Type*} [Category* A] [Category* C] (F : A ⥤ C)
    {I K : A} {I' K' : C} (e : F.obj I ≅ I') (x : I ⟶ K)
    (w : F.obj K ⟶ K') (m : I' ⟶ K') : Prop :=
  m = e.inv ≫ F.map x ≫ w

section Value

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {U : A ⥤ C} {V : B ⥤ D}
  [R₁.CommShift ℤ] [R₂.CommShift ℤ] [U.CommShift ℤ]

/-- The value of the original exchange on two shifted adjuncts with the
specified source and target transports. -/
def ShiftedMateValue (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (d : R₁ ⋙ U ⟶ V ⋙ R₂)
    {I : A} {J K : B} {I' : C} {J' K' : D}
    (e : L₁.obj I ≅ J) (e' : L₂.obj I' ≅ J') (u : U.obj I ≅ I') (t : V.obj K ≅ K')
    {q : ℤ} (x : ShiftedHom J K q) (y : ShiftedHom J' K' q) : Prop :=
  u.inv ≫ (adj₁.shiftedHomEquiv q I K (e.hom ≫ x)).map U ≫
    (d.app K)⟦q⟧' ≫ (R₂.map t.hom)⟦q⟧' =
      adj₂.shiftedHomEquiv q I' K' (e'.hom ≫ y)

/-- An original graded component is the inverse shift adjunct of the
specified original class. -/
def RegradedComponentValue (adj : L₂ ⊣ R₂)
    {I Iq : C} {J K : D} (e : L₂.obj I ≅ J) {q : ℤ}
    (η : I⟦-q⟧ ≅ Iq) (y : ShiftedHom J K q) (m : Iq ⟶ R₂.obj K) : Prop :=
  let a : shiftFunctor C (-q) ⊣ shiftFunctor C q :=
    (shiftEquiv' C (-q) q (neg_add_cancel q)).toAdjunction
  m = η.inv ≫ (a.homEquiv I (R₂.obj K)).symm
    (adj.shiftedHomEquiv q I K (e.hom ≫ y))

/-- The original shift regrading evaluates a graded component using a
value equation for the original exchange. -/
theorem regradedComponent_of_shiftedMateValue (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (d : R₁ ⋙ U ⟶ V ⋙ R₂)
    {I Iq : A} {J K : B} {I' Iq' : C} {J' K' : D}
    (e : L₁.obj I ≅ J) (e' : L₂.obj I' ≅ J') (u : U.obj I ≅ I') (t : V.obj K ≅ K')
    {q : ℤ} (x : ShiftedHom J K q) (y : ShiftedHom J' K' q)
    (h : ShiftedMateValue adj₁ adj₂ d e e' u t x y)
    (η : I⟦-q⟧ ≅ Iq) (η' : I'⟦-q⟧ ≅ Iq')
    {c : Iq ⟶ R₁.obj K}
    (hc : RegradedComponentValue adj₁ e η x c)
    {m : Iq' ⟶ R₂.obj K'}
    (hm : TransportedComponentValue U (U.shiftedSingleIsoOfIso q η η' u)
      c (d.app K ≫ R₂.map t.hom) m) :
    RegradedComponentValue adj₂ e' η' y m := by
  dsimp only [RegradedComponentValue, TransportedComponentValue] at hc hm ⊢
  let a : shiftFunctor C (-q) ⊣ shiftFunctor C q :=
    (shiftEquiv' C (-q) q (neg_add_cancel q)).toAdjunction
  rw [hm, hc]
  let w : U.obj (R₁.obj K) ⟶ R₂.obj K' := d.app K ≫ R₂.map t.hom
  let z := adj₁.shiftedHomEquiv q I K (e.hom ≫ x)
  have hr := U.shiftedSingleIsoOfIso_inv_comp q η η' u w z
  have hw : w⟦q⟧' = (d.app K)⟦q⟧' ≫ (R₂.map t.hom)⟦q⟧' :=
    (shiftFunctor C q).map_comp _ _
  have hh : u.inv ≫ z.map U ≫ w⟦q⟧' =
      adj₂.shiftedHomEquiv q I' K' (e'.hom ≫ y) := by
    rw [hw]
    exact h
  exact hr.trans (congrArg (fun v => η'.inv ≫ (a.homEquiv I' (R₂.obj K')).symm v) hh)

/-- The same original shifted value with explicitly identified unit transports. -/
theorem ShiftedMateValue.transport (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (d : R₁ ⋙ U ⟶ V ⋙ R₂) {I : A} {J K : B} {I' : C} {J' K' : D}
    {e₀ e : L₁.obj I ≅ J} {e₀' e' : L₂.obj I' ≅ J'}
    {u₀ u : U.obj I ≅ I'} {t₀ t : V.obj K ≅ K'}
    {q : ℤ} {x : ShiftedHom J K q} {y : ShiftedHom J' K' q}
    (h : ShiftedMateValue adj₁ adj₂ d e₀ e₀' u₀ t₀ x y)
    (he : e = e₀) (he' : e' = e₀') (hu : u = u₀) (ht : t = t₀) :
    ShiftedMateValue adj₁ adj₂ d e e' u t x y := by
  subst e
  subst e'
  subst u
  subst t
  exact h

/-- Identify the target shifted arrow by its original pullback equation. -/
theorem ShiftedMateValue.target_eq (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (d : R₁ ⋙ U ⟶ V ⋙ R₂) {I : A} {J K : B} {I' : C} {J' K' : D}
    {e : L₁.obj I ≅ J} {e' : L₂.obj I' ≅ J'} {u : U.obj I ≅ I'} {t : V.obj K ≅ K'}
    {q : ℤ} {x : ShiftedHom J K q} {y₀ y : ShiftedHom J' K' q}
    (h : ShiftedMateValue adj₁ adj₂ d e e' u t x y₀) (hy : y = y₀) :
    ShiftedMateValue adj₁ adj₂ d e e' u t x y := by
  subst y
  exact h

end Value

end CategoryTheory

namespace CategoryTheory

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {U : A ⥤ C} {V : B ⥤ D}

variable [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
  [R₁.CommShift ℤ] [R₂.CommShift ℤ] [U.CommShift ℤ] [V.CommShift ℤ]

/-- Naturality and the shift law carry the normalized unit adjunct to the
original shifted value. -/
theorem shiftedMateValue_of_unitAdjunct (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (d : R₁ ⋙ U ⟶ V ⋙ R₂) [NatTrans.CommShift d ℤ]
    {I : A} {J K : B} {I' : C} {J' K' : D}
    (e : L₁.obj I ≅ J) (e' : L₂.obj I' ≅ J')
    (u : U.obj I ≅ I') (v : V.obj J ≅ J') (t : V.obj K ≅ K')
    (h : UnitAdjunctValue adj₁ adj₂ d e e' u v)
    {q : ℤ} (x : ShiftedHom J K q) (y : ShiftedHom J' K' q)
    (hy : y = v.inv ≫ x.map V ≫ t.hom⟦q⟧') :
    ShiftedMateValue adj₁ adj₂ d e e' u t x y := by
  dsimp only [UnitAdjunctValue] at h
  let a := adj₁.homEquiv I J e.hom
  let b := adj₂.homEquiv I' J' e'.hom
  have hv : u.inv ≫ U.map a ≫ d.app J = b ≫ R₂.map v.inv := by
    apply (cancel_mono (R₂.map v.hom)).mp
    simp only [Category.assoc, ← R₂.map_comp, v.inv_hom_id, R₂.map_id, Category.comp_id]
    exact h
  have hs := NatTrans.shift_app_comm d q K
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hs
  have hn := d.naturality (show J ⟶ K⟦q⟧ from x)
  change U.map (R₁.map x) ≫ d.app (K⟦q⟧) = d.app J ≫ R₂.map (V.map x) at hn
  have h₀ : adj₁.shiftedHomEquiv q I K (e.hom ≫ x) =
      a ≫ R₁.map x ≫ (R₁.commShiftIso q).hom.app K := by
    rw [Adjunction.shiftedHomEquiv_apply, adj₁.homEquiv_naturality_right]
    exact Category.assoc _ _ _
  have h₁ : adj₂.shiftedHomEquiv q I' K' (e'.hom ≫ y) =
      b ≫ R₂.map y ≫ (R₂.commShiftIso q).hom.app K' := by
    rw [Adjunction.shiftedHomEquiv_apply, adj₂.homEquiv_naturality_right]
    exact Category.assoc _ _ _
  dsimp only [ShiftedMateValue]
  rw [h₀, h₁, hy]
  simp only [ShiftedHom.map, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hs, ← Category.assoc (U.map (R₁.map x)), hn]
  simp only [Category.assoc]
  rw [reassoc_of% hv, ← R₂.commShiftIso_hom_naturality t.hom q]

end CategoryTheory
