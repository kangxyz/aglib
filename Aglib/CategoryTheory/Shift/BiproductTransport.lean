/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Shift.AdjunctValue
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! Original biproduct transport and its homogeneous component values. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

/-- A mapped biproduct descent retains the original transported components. -/
theorem CategoryTheory.Limits.biproduct.mapIso_inv_mapBiproduct_inv_map_desc_ι
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    {I : Type} (F : C ⥤ D) [F.PreservesZeroMorphisms] (P : I → C) (Q : I → D)
    [HasBiproduct P] [HasBiproduct Q] [PreservesBiproduct P F]
    (e : ∀ i, F.obj (P i) ≅ Q i) {K : C} {W : D}
    (x : ∀ i, P i ⟶ K) (m : (⨁ P) ⟶ K) (hm : m = biproduct.desc x)
    (w : F.obj K ⟶ W) (i : I) :
    TransportedComponentValue F (e i) (x i) w
      (biproduct.ι Q i ≫ (biproduct.mapIso e).inv ≫ (F.mapBiproduct P).inv ≫ F.map m ≫ w) := by
  dsimp only [TransportedComponentValue]
  subst m
  simp only [biproduct.mapIso_inv, biproduct.ι_map_assoc, Functor.mapBiproduct_inv,
    biproduct.ι_desc_assoc, ← Functor.map_comp_assoc, biproduct.ι_desc]

namespace CategoryTheory

open Limits

/-- Transport a finite sum map through the original functor and component comparisons. -/
def Functor.transportBiproduct {A C : Type*} [Category* A] [Category* C]
    [HasZeroMorphisms A] [HasZeroMorphisms C] {I : Type}
    (F : A ⥤ C) [F.PreservesZeroMorphisms] (P : I → A) (Q : I → C)
    [HasBiproduct P] [HasBiproduct Q] [PreservesBiproduct P F]
    (a : ∀ i, F.obj (P i) ≅ Q i) {K : A} {W : C}
    (m : (⨁ P) ⟶ K) (w : F.obj K ⟶ W) : (⨁ Q) ⟶ W :=
  (biproduct.mapIso a).inv ≫ (F.mapBiproduct P).inv ≫ F.map m ≫ w

/-- Regrading evaluates the original transported biproduct component in one step. -/
theorem regradedComponent_of_shiftedMateValue_biproduct
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    [HasZeroMorphisms A] [HasZeroMorphisms C]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {U : A ⥤ C} {V : B ⥤ D}
    [R₁.CommShift ℤ] [R₂.CommShift ℤ] [U.CommShift ℤ] [U.PreservesZeroMorphisms]
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (β : R₁ ⋙ U ⟶ V ⋙ R₂)
    {I₀ : A} {J K : B} {I₀' : C} {J' K' : D}
    (e : L₁.obj I₀ ≅ J) (e' : L₂.obj I₀' ≅ J') (u : U.obj I₀ ≅ I₀') (t : V.obj K ≅ K')
    {d : ℤ} (x : ShiftedHom J K d) (y : ShiftedHom J' K' d)
    (hs : ShiftedMateValue adj₁ adj₂ β e e' u t x y)
    {I : Type} (P : I → A) (Q : I → C) (i : I)
    [HasBiproduct P] [HasBiproduct Q] [PreservesBiproduct P U]
    (a : ∀ j, U.obj (P j) ≅ Q j) (η : I₀⟦-d⟧ ≅ P i) (η' : I₀'⟦-d⟧ ≅ Q i)
    (ha : a i = U.shiftedSingleIsoOfIso d η η' u)
    (c : ∀ j, P j ⟶ R₁.obj K)
    (hc : RegradedComponentValue adj₁ e η x (c i))
    (m : (⨁ P) ⟶ R₁.obj K) (hm : m = biproduct.desc c) :
    RegradedComponentValue adj₂ e' η' y
      (biproduct.ι Q i ≫ U.transportBiproduct P Q a m (β.app K ≫ R₂.map t.hom)) := by
  let w := β.app K ≫ R₂.map t.hom
  have ht := biproduct.mapIso_inv_mapBiproduct_inv_map_desc_ι U P Q a c m hm w i
  rw [ha] at ht
  apply regradedComponent_of_shiftedMateValue adj₁ adj₂ β e e' u t x y hs η η' hc
  simpa only [Functor.transportBiproduct, Category.assoc] using ht

end CategoryTheory
