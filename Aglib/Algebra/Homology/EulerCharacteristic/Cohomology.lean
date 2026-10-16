/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.EulerCharacteristic

/-!
# Finite sums for the native homological Euler characteristic

Cohomological bounds suffice to bound the rank support of the original
homology objects. The existing integer-indexed homological Euler
characteristic is consequently the finite alternating sum over the
same interval. For a complex supported cohomologically in `[0,n]`, the
formula uses the usual natural-degree signs and degrees `0` through `n`.
No finiteness or strict termwise bound is needed for these identities.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Module

namespace CochainComplex

universe u v

variable {R : Type u} [Ring R] [Nontrivial R] (C : CochainComplex (ModuleCat.{v} R) ℤ)

/-- Cohomological bounds contain the rank support of the original homology objects. -/
theorem homology_finrankSupport_subset_Icc (a b : ℤ) [C.IsGE a] [C.IsLE b] :
    GradedObject.finrankSupport (fun i => C.homology i) ⊆ Set.Icc a b := by
  intro i hi
  change finrank R (C.homology i) ≠ 0 at hi
  constructor
  · by_contra h
    let : Subsingleton (C.homology i) :=
      ModuleCat.subsingleton_of_isZero (C.isZero_of_isGE a i (by omega))
    exact hi Module.finrank_zero_of_subsingleton
  · by_contra h
    let : Subsingleton (C.homology i) :=
      ModuleCat.subsingleton_of_isZero (C.isZero_of_isLE b i (by omega))
    exact hi Module.finrank_zero_of_subsingleton

/-- A cohomologically bounded complex has finite native homological rank support. -/
theorem finite_homology_finrankSupport (a b : ℤ) [C.IsGE a] [C.IsLE b] :
    (GradedObject.finrankSupport (fun i => C.homology i)).Finite :=
  (Set.finite_Icc a b).subset (C.homology_finrankSupport_subset_Icc a b)

/-- The native homological Euler characteristic is its finite sum on any interval
containing the original cohomology. -/
theorem homologyEulerChar_eq_sum_Icc (a b : ℤ) [C.IsGE a] [C.IsLE b] :
    HomologicalComplex.homologyEulerChar C =
      ∑ i ∈ Finset.Icc a b, ((ComplexShape.up ℤ).χ i : ℤ) *
        (finrank R (C.homology i) : ℤ) := by
  apply C.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset
  simpa only [Finset.coe_Icc] using C.homology_finrankSupport_subset_Icc a b

/-- For nonnegative cohomological support, the native integer-indexed Euler
characteristic is the usual alternating sum over the original natural degrees. -/
theorem homologyEulerChar_eq_sum_range (n : ℕ) [C.IsGE 0] [C.IsLE (n : ℤ)] :
    HomologicalComplex.homologyEulerChar C =
      ∑ q ∈ Finset.range (n + 1), (-1 : ℤ) ^ q *
        (finrank R (C.homology (q : ℤ)) : ℤ) := by
  rw [C.homologyEulerChar_eq_sum_Icc 0 (n : ℤ), Int.Icc_eq_finset_map,
    Finset.sum_map]
  simp only [sub_zero, Int.toNat_natCast_add_one, Function.Embedding.trans_apply,
    Nat.castEmbedding_apply, addLeftEmbedding_apply, zero_add,
    ComplexShape.eulerCharSignsUpInt_χ, Int.reduceNeg]
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  exact congrArg (fun j : ℤ => (finrank R (C.homology j) : ℤ)) (zero_add (q : ℤ))

end CochainComplex
