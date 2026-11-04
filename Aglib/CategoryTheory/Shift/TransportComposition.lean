/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Shift.ShiftedHom

/-! The original shifted composition under the original endpoint transports. -/

open CategoryTheory

@[expose] public noncomputable section

namespace CategoryTheory.ShiftedHom

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]

/-- Original shifted composition cancels the middle comparison and keeps the endpoint maps. -/
theorem comp_transport_values
    {A B K A' B' K' : C} (u : A' ⟶ A) (e : B ≅ B') (v : K ⟶ K')
    {p q d : ℤ} (x : ShiftedHom A B p) (y : ShiftedHom B K q) (h : q + p = d) :
    ShiftedHom.comp (u ≫ x ≫ e.hom⟦p⟧' : ShiftedHom A' B' p)
        (e.inv ≫ y ≫ v⟦q⟧' : ShiftedHom B' K' q) h =
      u ≫ x.comp y h ≫ v⟦d⟧' := by
  let H := shiftFunctor C p
  let T := shiftFunctorAdd' C q p d h
  have hn : H.map (v⟦q⟧') ≫ T.inv.app K' =
      T.inv.app K ≫ v⟦d⟧' := T.inv.naturality v
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]
  change u ≫ x ≫ H.map e.hom ≫ H.map e.inv ≫ H.map y ≫
    H.map (v⟦q⟧') ≫ T.inv.app K' =
      u ≫ x ≫ H.map y ≫ T.inv.app K ≫ v⟦d⟧'
  rw [← H.map_comp_assoc e.hom e.inv, e.hom_inv_id, H.map_id, Category.id_comp, hn]

/-- Mapping the original composition and transporting the endpoints retains its given value. -/
theorem map_comp_transport_value (F : C ⥤ D) [F.CommShift ℤ]
    {A B K : C} {A' B' K' : D} (u : A' ⟶ F.obj A) (e : F.obj B ≅ B')
    (v : F.obj K ⟶ K') {p q d : ℤ} (x : ShiftedHom A B p) (y : ShiftedHom B K q)
    (h : q + p = d) (z : ShiftedHom A K d) (hz : x.comp y h = z)
    (x' : ShiftedHom A' B' p) (hx : x' = u ≫ x.map F ≫ e.hom⟦p⟧') :
    x'.comp (e.inv ≫ y.map F ≫ v⟦q⟧' : ShiftedHom B' K' q) h =
      u ≫ z.map F ≫ v⟦d⟧' := by
  rw [hx, comp_transport_values, ← ShiftedHom.map_comp, hz]

end CategoryTheory.ShiftedHom

namespace CategoryTheory.ShiftedHom

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]

/-- The transported shifted composite has the given original target value. -/
theorem map_comp_transport_of_values (F : C ⥤ D) [F.CommShift ℤ]
    {A B K : C} {A' B' K' : D} (u : A' ⟶ F.obj A) (e : F.obj B ≅ B')
    (v : F.obj K ⟶ K') {p q d : ℤ} (x : ShiftedHom A B p) (y : ShiftedHom B K q)
    (h : q + p = d) (z : ShiftedHom A K d) (hz : x.comp y h = z)
    (x' : ShiftedHom A' B' p) (hx : x' = u ≫ x.map F ≫ e.hom⟦p⟧')
    (z' : ShiftedHom A' K' d) (hz' : z' = u ≫ z.map F ≫ v⟦d⟧') :
    x'.comp (e.inv ≫ y.map F ≫ v⟦q⟧' : ShiftedHom B' K' q) h = z' :=
  (map_comp_transport_value F u e v x y h z hz x' hx).trans hz'.symm

/-- A comparison of the original shifted connecting maps retains the
whole trace composite after the original source restriction. -/
theorem comp_trace_of_square
    {I B₀ B F₀ F J : D} {r s q d : ℤ}
    (x : ShiftedHom I B₀ r) (δ₀ : ShiftedHom B₀ F₀ s)
    (b : B₀ ⟶ B) (a : F₀ ⟶ F) (δ : ShiftedHom B F s)
    (h : b ≫ δ = δ₀ ≫ a⟦s⟧')
    (t : ShiftedHom F J q) (hd : q + s + r = d) :
    (ShiftedHom.comp (x ≫ b⟦r⟧' : ShiftedHom I B r) δ (rfl : s + r = s + r)).comp
        t (by omega : q + (s + r) = d) =
      (x.comp δ₀ (rfl : s + r = s + r)).comp (a ≫ t : ShiftedHom F₀ J q)
        (by omega : q + (s + r) = d) := by
  let b₀ := ShiftedHom.mk₀ (0 : ℤ) rfl b
  let a₀ := ShiftedHom.mk₀ (0 : ℤ) rfl a
  have hx : x.comp b₀ (zero_add r) = x ≫ b⟦r⟧' := ShiftedHom.comp_mk₀ x 0 rfl b
  have hδ : b₀.comp δ (add_zero s) = δ₀.comp a₀ (zero_add s) := by
    exact (ShiftedHom.mk₀_comp 0 rfl b δ).trans (h.trans (ShiftedHom.comp_mk₀ δ₀ 0 rfl a).symm)
  have ht : a₀.comp t (add_zero q) = a ≫ t := ShiftedHom.mk₀_comp 0 rfl a t
  rw [← hx, ShiftedHom.comp_assoc x b₀ δ (zero_add r) (add_zero s) (by omega),
    hδ, ← ShiftedHom.comp_assoc x δ₀ a₀ (rfl : s + r = s + r) (zero_add s) (by omega),
    ShiftedHom.comp_assoc (x.comp δ₀ rfl) a₀ t (zero_add (s + r)) (add_zero q) (by omega),
    ht]

end CategoryTheory.ShiftedHom
