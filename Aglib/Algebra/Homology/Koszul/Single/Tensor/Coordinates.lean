/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

public import Aglib.Algebra.Homology.Koszul.Basic

/-!
# Two-column coordinates for a one-element Koszul tensor

Tensoring an arbitrary nonnegative complex with a one-element multiplication
complex has two nonzero columns. This file gives actual inclusions, projections,
and the resulting two-column splitting of each term.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R] (a : R) (K : ChainComplex (ModuleCat.{u} R) ℕ)

/-- The old-complex column of a one-element tensor. -/
noncomputable def singleTensorιZero (n : ℕ) :
    K.X n ⟶ (HomologicalComplex.tensorObj (singleComplex R a) K).X n :=
  (λ_ (K.X n)).inv ≫ HomologicalComplex.ιTensorObj (singleComplex R a) K 0 n n (by omega)

/-- The shifted column of a one-element tensor. -/
noncomputable def singleTensorιOne (n : ℕ) :
    K.X n ⟶ (HomologicalComplex.tensorObj (singleComplex R a) K).X (n + 1) :=
  (λ_ (K.X n)).inv ≫
    HomologicalComplex.ιTensorObj (singleComplex R a) K 1 n (n + 1) (by omega)

/-- Projection onto the old-complex column. -/
noncomputable def singleTensorπZero (n : ℕ) :
    (HomologicalComplex.tensorObj (singleComplex R a) K).X n ⟶ K.X n :=
  HomologicalComplex.mapBifunctorDesc (fun i j h => by
    change i + j = n at h
    cases i with
    | zero =>
      have hj : j = n := by omega
      subst j
      exact (λ_ (K.X n)).hom
    | succ i => exact 0)

/-- Projection onto the shifted column. -/
noncomputable def singleTensorπOne (n : ℕ) :
    (HomologicalComplex.tensorObj (singleComplex R a) K).X (n + 1) ⟶ K.X n :=
  HomologicalComplex.mapBifunctorDesc (fun i j h => by
    change i + j = n + 1 at h
    obtain (_ | _ | i) := i
    · exact 0
    · have hj : j = n := by omega
      subst j
      exact (λ_ (K.X n)).hom
    · exact 0)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem singleTensorιZero_πZero (n : ℕ) :
    singleTensorιZero a K n ≫ singleTensorπZero a K n = 𝟙 _ := by
  simp [Category.assoc, singleTensorιZero, singleTensorπZero]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem singleTensorιOne_πOne (n : ℕ) :
    singleTensorιOne a K n ≫ singleTensorπOne a K n = 𝟙 _ := by
  simp [Category.assoc, singleTensorιOne, singleTensorπOne]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem singleTensorιZero_πOne (n : ℕ) :
    singleTensorιZero a K (n + 1) ≫ singleTensorπOne a K n = 0 := by
  simp [Category.assoc, singleTensorιZero, singleTensorπOne]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem singleTensorιOne_πZero (n : ℕ) :
    singleTensorιOne a K n ≫ singleTensorπZero a K (n + 1) = 0 := by
  simp [Category.assoc, singleTensorιOne, singleTensorπZero]

set_option backward.isDefEq.respectTransparency false in
/-- In positive degrees the two column inclusions and projections split the term. -/
theorem singleTensor_decomposition (n : ℕ) :
    singleTensorπZero a K (n + 1) ≫ singleTensorιZero a K (n + 1) +
      singleTensorπOne a K n ≫ singleTensorιOne a K n = 𝟙 _ := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  change i + j = n + 1 at h
  obtain (_ | _ | i) := i
  · have hj : j = n + 1 := by omega
    subst j
    simp [singleTensorπZero, singleTensorπOne, singleTensorιZero, Preadditive.comp_add]
  · have hj : j = n := by omega
    subst j
    simp [singleTensorπZero, singleTensorπOne, singleTensorιOne, Preadditive.comp_add]
  · have hz : IsZero ((singleComplex R a).X (i + 2) ⊗ K.X j) :=
      Functor.map_isZero ((tensoringRight (ModuleCat R)).obj (K.X j)) (isZero_zero _)
    exact hz.eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
/-- Degree zero consists of the old-complex column alone. -/
@[reassoc (attr := simp)]
theorem singleTensor_decomposition_zero :
    singleTensorπZero a K 0 ≫ singleTensorιZero a K 0 = 𝟙 _ := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  change i + j = 0 at h
  have hi : i = 0 := by omega
  have hj : j = 0 := by omega
  subst i j
  simp [singleTensorπZero, singleTensorιZero]

/-- Maps out of a positive-degree term are determined on its two columns. -/
theorem singleTensor_hom_ext {A : ModuleCat.{u} R} (n : ℕ)
    {f g : (HomologicalComplex.tensorObj (singleComplex R a) K).X (n + 1) ⟶ A}
    (h₀ : singleTensorιZero a K (n + 1) ≫ f = singleTensorιZero a K (n + 1) ≫ g)
    (h₁ : singleTensorιOne a K n ≫ f = singleTensorιOne a K n ≫ g) : f = g := by
  have h := congrArg (fun p => p ≫ f) (singleTensor_decomposition a K n)
  have h' := congrArg (fun p => p ≫ g) (singleTensor_decomposition a K n)
  simp only [Preadditive.add_comp, Category.assoc, Category.id_comp] at h h'
  rw [h₀, h₁] at h
  exact h.symm.trans h'

/-- Maps out of degree zero are determined on its old-complex column. -/
theorem singleTensor_hom_ext_zero {A : ModuleCat.{u} R}
    {f g : (HomologicalComplex.tensorObj (singleComplex R a) K).X 0 ⟶ A}
    (h : singleTensorιZero a K 0 ≫ f = singleTensorιZero a K 0 ≫ g) : f = g := by
  simpa using congrArg (fun p => singleTensorπZero a K 0 ≫ p) h

end ChainComplex.Koszul
