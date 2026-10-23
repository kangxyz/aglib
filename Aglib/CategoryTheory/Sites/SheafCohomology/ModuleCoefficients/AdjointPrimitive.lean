/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-! # Transporting an actual primitive through an additive adjunction -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

universe v u v' u'

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive]

/-- Degree-one exactness of the original additive Hom complex produces a
primitive after applying an additive left adjoint. -/
theorem exists_primitive_of_adjoint_exact (adj : L ⊣ R)
    (K : ChainComplex C ℕ) (F : D)
    (hex : (((preadditiveYoneda.obj (R.obj F)).mapHomologicalComplex (.up ℕ)).obj
      K.op).ExactAt 1)
    (z : L.obj (K.X 1) ⟶ F) (hz : L.map (K.d 2 1) ≫ z = 0) :
    ∃ a : L.obj (K.X 0) ⟶ F, L.map (K.d 1 0) ≫ a = z := by
  let M := ((preadditiveYoneda.obj (R.obj F)).mapHomologicalComplex (.up ℕ)).obj K.op
  have he : (M.sc' 0 1 2).Exact :=
    (HomologicalComplex.exactAt_iff' M 0 1 2 (by simp) (by simp)).1 hex
  have hz' : K.d 2 1 ≫ adj.homEquiv _ F z = 0 := by
    rw [← adj.homEquiv_naturality_left, hz, adj.homAddEquiv_zero]
  obtain ⟨a, ha⟩ := (ShortComplex.ab_exact_iff _).1 he (adj.homEquiv _ F z) hz'
  change K.X 0 ⟶ R.obj F at a
  change K.d 1 0 ≫ a = adj.homEquiv _ F z at ha
  refine ⟨(adj.homEquiv _ F).symm a, ?_⟩
  apply (adj.homEquiv _ F).injective
  rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
  exact ha

end CategoryTheory.Sheaf.ModuleCoefficients
