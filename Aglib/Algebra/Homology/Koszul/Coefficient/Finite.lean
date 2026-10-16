/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

public import Aglib.Algebra.Homology.Koszul.Coefficient
public import Aglib.Algebra.Homology.Koszul.Single.Tensor.Elements
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Finiteness and coefficient support of finite Koszul complexes

The two-column splitting proves that every term of the actual finite coefficient
Koszul complex is finite when its coefficient module is finite. Over a
Noetherian ring the actual homology modules are consequently finite. The
coefficient annihilator kills every term and every homology module, without
regularity hypotheses.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]

/-- Every term of a coefficient Koszul complex is finite over the base ring. -/
instance coefficient_finite_X (M : ModuleCat R) [Module.Finite R M] (s : List R) (n : ℕ) :
    Module.Finite R ((coefficientComplex M s).X n) := by
  induction s generalizing n with
  | nil =>
    cases n with
    | zero => exact inferInstanceAs (Module.Finite R M)
    | succ n =>
      have : Subsingleton ((coefficientComplex M []).X (n + 1)) :=
        ModuleCat.subsingleton_of_isZero
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 M (n + 1) (by omega))
      infer_instance
  | cons a s ih =>
    cases n with
    | zero =>
      have := ih 0
      apply Module.Finite.of_surjective (singleTensorιZero a (coefficientComplex M s) 0).hom
      intro x
      exact ⟨singleTensorπZero a (coefficientComplex M s) 0 x,
        singleTensor_decomposition_zero_apply a (coefficientComplex M s) x⟩
    | succ n =>
      have := ih n
      have := ih (n + 1)
      apply Module.Finite.of_surjective
        ((singleTensorιZero a (coefficientComplex M s) (n + 1)).hom.coprod
          (singleTensorιOne a (coefficientComplex M s) n).hom)
      intro x
      exact ⟨(singleTensorπZero a (coefficientComplex M s) (n + 1) x,
        singleTensorπOne a (coefficientComplex M s) n x),
        singleTensor_decomposition_apply a (coefficientComplex M s) n x⟩

/-- Every original ring Koszul term is finite, without Noetherianity or regularity. -/
instance chainComplex_finite_X (s : List R) (n : ℕ) :
    Module.Finite R ((chainComplex s).X n) := by
  rw [← coefficientComplex_ring s]
  infer_instance

/-- The actual homology of a finite coefficient Koszul complex is Noetherian. -/
instance coefficient_noetherian_homology [IsNoetherianRing R] (M : ModuleCat R)
    [Module.Finite R M] (s : List R) (n : ℕ) :
    IsNoetherian R ((coefficientComplex M s).homology n) := by
  have : IsNoetherian R ((coefficientComplex M s).cycles n) :=
    isNoetherian_of_injective ((coefficientComplex M s).iCycles n).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact isNoetherian_of_surjective ((coefficientComplex M s).homologyπ n).hom
    (LinearMap.range_eq_top.mpr ((ModuleCat.epi_iff_surjective _).mp inferInstance))

/-- The coefficient annihilator kills each term of the actual finite complex. -/
theorem coefficient_annihilator_le_annihilator_X (M : ModuleCat R) (s : List R) (n : ℕ) :
    Module.annihilator R M ≤ Module.annihilator R ((coefficientComplex M s).X n) := by
  intro a ha
  apply Module.mem_annihilator.mpr
  intro x
  induction s generalizing n with
  | nil =>
    cases n with
    | zero => exact Module.mem_annihilator.mp ha x
    | succ n =>
      have : Subsingleton ((coefficientComplex M []).X (n + 1)) :=
        ModuleCat.subsingleton_of_isZero
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 M (n + 1) (by omega))
      exact Subsingleton.elim _ _
  | cons b s ih =>
    cases n with
    | zero =>
      apply singleTensor_ext_zero b (coefficientComplex M s)
      change (singleTensorπZero b (coefficientComplex M s) 0).hom (a • x) =
        (singleTensorπZero b (coefficientComplex M s) 0).hom 0
      exact ((singleTensorπZero b (coefficientComplex M s) 0).hom.map_smul a x).trans
        ((ih 0 _).trans ((singleTensorπZero b (coefficientComplex M s) 0).hom.map_zero).symm)
    | succ n =>
      apply singleTensor_ext b (coefficientComplex M s) n
      · change (singleTensorπZero b (coefficientComplex M s) (n + 1)).hom (a • x) =
          (singleTensorπZero b (coefficientComplex M s) (n + 1)).hom 0
        exact ((singleTensorπZero b (coefficientComplex M s) (n + 1)).hom.map_smul a x).trans
          ((ih (n + 1) _).trans
            ((singleTensorπZero b (coefficientComplex M s) (n + 1)).hom.map_zero).symm)
      · change (singleTensorπOne b (coefficientComplex M s) n).hom (a • x) =
          (singleTensorπOne b (coefficientComplex M s) n).hom 0
        exact ((singleTensorπOne b (coefficientComplex M s) n).hom.map_smul a x).trans
          ((ih n _).trans ((singleTensorπOne b (coefficientComplex M s) n).hom.map_zero).symm)

/-- The coefficient annihilator kills the actual finite Koszul homology. -/
theorem coefficient_annihilator_le_annihilator_homology
    (M : ModuleCat R) (s : List R) (n : ℕ) :
    Module.annihilator R M ≤ Module.annihilator R ((coefficientComplex M s).homology n) :=
  (coefficient_annihilator_le_annihilator_X M s n).trans
    ((((coefficientComplex M s).iCycles n).hom.annihilator_le_of_injective
      ((ModuleCat.mono_iff_injective _).mp inferInstance)).trans
      (((coefficientComplex M s).homologyπ n).hom.annihilator_le_of_surjective
        ((ModuleCat.epi_iff_surjective _).mp inferInstance)))

end ChainComplex.Koszul
