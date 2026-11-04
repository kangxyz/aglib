/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.UnderlyingHomEquiv
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Shift.ShiftedHom

/-! The original adjunction and mate equations on native shifted Hom. -/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D]
  {M : Type*} [AddMonoid M] [HasShift C M] [HasShift D M]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [R.CommShift M]

/-- The actual adjunction on original shifted morphisms. -/
noncomputable def shiftedHomEquiv (a : M) (X : C) (Y : D) :
    ShiftedHom (L.obj X) Y a ≃ ShiftedHom X (R.obj Y) a :=
  (adj.homEquiv X (Y⟦a⟧)).trans
    ((Iso.refl X).homCongr ((R.commShiftIso a).app Y))

/-- The shifted value retains the actual adjunction followed by the right shift comparison. -/
theorem shiftedHomEquiv_apply {X : C} {Y : D} {a : M} (f : ShiftedHom (L.obj X) Y a) :
    adj.shiftedHomEquiv a X Y f =
      adj.homEquiv X (Y⟦a⟧) f ≫ (R.commShiftIso a).hom.app Y := by
  change 𝟙 X ≫ _ = _
  exact Category.id_comp _

variable [L.CommShift M] [adj.CommShift M]

/-- The inverse of the original shifted adjunction is evaluation at the original counit. -/
theorem shiftedHomEquiv_symm_apply {X : C} {Y : D} {a : M} (f : ShiftedHom X (R.obj Y) a) :
    (adj.shiftedHomEquiv a X Y).symm f =
      (f.map L).comp (ShiftedHom.mk₀ 0 rfl (adj.counit.app Y)) (zero_add a) := by
  change (adj.homEquiv X (Y⟦a⟧)).symm (𝟙 X ≫ f ≫ (R.commShiftIso a).inv.app Y) = _
  rw [Category.id_comp, adj.homEquiv_counit, Functor.map_comp, Category.assoc]
  have h := adj.commShiftIso_hom_app_counit_app_shift M a Y
  rw [Functor.commShiftIso_comp_hom_app] at h
  rw [← h]
  simp only [Category.assoc]
  rw [← L.map_comp_assoc ((R.commShiftIso a).inv.app Y) ((R.commShiftIso a).hom.app Y),
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  rw [ShiftedHom.comp_mk₀, ShiftedHom.map, Category.assoc]

/-- Precomposition in the shifted adjunction uses the original shifted pullback and product. -/
theorem shiftedHomEquiv_comp_map {X X' : C} {Y : D} {a b c : M}
    (x : ShiftedHom X X' a) (y : ShiftedHom (L.obj X') Y b) (h : b + a = c) :
    adj.shiftedHomEquiv c X Y ((x.map L).comp y h) =
      x.comp (adj.shiftedHomEquiv b X' Y y) h := by
  let z := adj.shiftedHomEquiv b X' Y y
  let e := ShiftedHom.mk₀ (0 : M) rfl (adj.counit.app Y)
  have hz : (z.map L).comp e (zero_add b) = y :=
    (adj.shiftedHomEquiv_symm_apply z).symm.trans
      ((adj.shiftedHomEquiv b X' Y).symm_apply_apply y)
  apply (adj.shiftedHomEquiv c X Y).symm.injective
  rw [Equiv.symm_apply_apply, adj.shiftedHomEquiv_symm_apply, ShiftedHom.map_comp]
  change (x.map L).comp y h = ((x.map L).comp (z.map L) h).comp e (zero_add c)
  rw [ShiftedHom.comp_assoc (x.map L) (z.map L) e h (zero_add b)
    (by rw [zero_add, h]), hz]

end CategoryTheory.Adjunction

namespace CategoryTheory

variable {A B C D M : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [AddMonoid M] [HasShift A M] [HasShift B M] [HasShift C M] [HasShift D M]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {U : A ⥤ C} {V : B ⥤ D}
  [R₁.CommShift M] [R₂.CommShift M] [U.CommShift M] [V.CommShift M]

/-- The original mate identifies the shifted adjunct after the original pullback. -/
theorem shiftedHomEquiv_of_mate (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (s : TwoSquare U L₁ L₂ V) (d : R₁ ⋙ U ⟶ V ⋙ R₂)
    [NatTrans.CommShift d M] (hd : (mateEquiv adj₁ adj₂ s).natTrans = d)
    (P : A) (Q : B) (a : M) (j : ShiftedHom (L₁.obj P) Q a) :
    (adj₁.shiftedHomEquiv a P Q j).map U ≫ (d.app Q)⟦a⟧' =
      adj₂.shiftedHomEquiv a (U.obj P) (V.obj Q) (s.app P ≫ j.map V) := by
  have hs := NatTrans.shift_app_comm d a Q
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hs
  have h := underlying_homEquiv_of_mate adj₁ adj₂ s d hd P (Q⟦a⟧) j
  simp only [Adjunction.shiftedHomEquiv_apply, ShiftedHom.map, Functor.map_comp, Category.assoc]
  rw [hs, ← Category.assoc (U.map (adj₁.homEquiv P (Q⟦a⟧) j)), h]
  simpa only [Category.assoc, Functor.comp_obj] using congrArg
    (fun z => z ≫ (R₂.commShiftIso a).hom.app (V.obj Q))
    (adj₂.homEquiv_naturality_right (s.app P ≫ V.map j)
      ((V.commShiftIso a).hom.app Q)).symm

end CategoryTheory

namespace CategoryTheory

variable {A B C D M : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [AddMonoid M] [HasShift A M] [HasShift B M] [HasShift C M] [HasShift D M]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {U : A ⥤ C} {V : B ⥤ D}
  [R₁.CommShift M] [R₂.CommShift M] [U.CommShift M] [V.CommShift M]

/-- The original shifted mate comparison with the actual unit and target transports. -/
theorem shiftedHomEquiv_of_mate_of_unitSquare (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (s : TwoSquare U L₁ L₂ V) (d : R₁ ⋙ U ⟶ V ⋙ R₂)
    [NatTrans.CommShift d M] (hd : (mateEquiv adj₁ adj₂ s).natTrans = d)
    {I : A} {J : B} {I' : C} {J' : D} {K : B} {K' : D}
    (e : L₁.obj I ≅ J) (e' : L₂.obj I' ≅ J')
    (u : U.obj I ≅ I') (v : V.obj J ≅ J') (t : V.obj K ≅ K')
    (h : s.app I ≫ V.map e.hom ≫ v.hom = L₂.map u.hom ≫ e'.hom)
    {q : M} (x : ShiftedHom J K q) :
    u.inv ≫ (adj₁.shiftedHomEquiv q I K (e.hom ≫ x)).map U ≫
        (d.app K)⟦q⟧' ≫ (R₂.map t.hom)⟦q⟧' =
      adj₂.shiftedHomEquiv q I' K' (e'.hom ≫ v.inv ≫ x.map V ≫ t.hom⟦q⟧') := by
  have hu : L₂.map u.inv ≫ s.app I ≫ V.map e.hom = e'.hom ≫ v.inv := by
    apply (cancel_mono v.hom).mp
    simp only [Category.assoc, v.inv_hom_id, Category.comp_id]
    rw [h, ← L₂.map_comp_assoc, u.inv_hom_id, L₂.map_id, Category.id_comp]
  have hm := shiftedHomEquiv_of_mate adj₁ adj₂ s d hd I K q (e.hom ≫ x)
  have hv : ShiftedHom.map (e.hom ≫ x : ShiftedHom (L₁.obj I) K q) V =
      V.map e.hom ≫ x.map V := by
    simp only [ShiftedHom.map, Functor.map_comp, Category.assoc]
  rw [hv] at hm
  rw [← Category.assoc ((adj₁.shiftedHomEquiv q I K (e.hom ≫ x)).map U), hm]
  simp only [Adjunction.shiftedHomEquiv_apply, Category.assoc]
  let z : L₂.obj (U.obj I) ⟶ (V.obj K)⟦q⟧ := s.app I ≫ V.map e.hom ≫ x.map V
  let t' := t.hom⟦q⟧'
  let φ := (R₂.commShiftIso q).hom.app K'
  have hz : L₂.map u.inv ≫ z ≫ t' = e'.hom ≫ v.inv ≫ x.map V ≫ t' := by
    dsimp only [z]
    simp only [Category.assoc]
    exact (reassoc_of% hu) (x.map V ≫ t')
  calc
    _ = u.inv ≫ adj₂.homEquiv (U.obj I) _ z ≫ R₂.map t' ≫ φ := by
      change u.inv ≫ adj₂.homEquiv (U.obj I) _ z ≫
        (R₂.commShiftIso q).hom.app (V.obj K) ≫ (R₂.map t.hom)⟦q⟧' = _
      rw [← R₂.commShiftIso_hom_naturality t.hom q]
    _ = u.inv ≫ adj₂.homEquiv (U.obj I) _ (z ≫ t') ≫ φ := by
      simpa only [Category.assoc] using congrArg
        (fun k => u.inv ≫ k ≫ φ) (adj₂.homEquiv_naturality_right z t').symm
    _ = adj₂.homEquiv I' _ (L₂.map u.inv ≫ z ≫ t') ≫ φ := by
      rw [adj₂.homEquiv_naturality_left]
      simp only [Category.assoc]
    _ = _ := by rw [hz]


end CategoryTheory

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D]
  {M : Type*} [AddMonoid M] [HasShift C M] [HasShift D M]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [R.CommShift M]

variable [L.CommShift M] [adj.CommShift M]

/-- A transported unit pullback gives the original shifted product after adjunction. -/
theorem shiftedHomEquiv_comp_map_of_unitIso {U : C} {V Y : D} {a b c : M}
    (i : L.obj U ≅ V) (x : ShiftedHom U U a) (y : ShiftedHom V Y b)
    (p : ShiftedHom V V a) (hp : p = i.inv ≫ x.map L ≫ i.hom⟦a⟧')
    (h : b + a = c) :
    adj.shiftedHomEquiv c U Y (i.hom ≫ p.comp y h) =
      x.comp (adj.shiftedHomEquiv b U Y (i.hom ≫ y)) h := by
  have he : i.hom ≫ p.comp y h = (x.map L).comp (i.hom ≫ y) h := by
    rw [hp]
    simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [he, adj.shiftedHomEquiv_comp_map]

end CategoryTheory.Adjunction
