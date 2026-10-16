/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.OptionSequence
public import Mathlib.LinearAlgebra.Pi

/-!
# The singleton base and positive-degree insertion exactness

Inserting an omitted vertex proves positive-degree exactness even for empty
required support. For a singleton vertex set every tuple has full support;
the native full-support complex therefore has scalar degree-zero homology
and vanishing positive homology. This is the base of vertex-removal induction.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v

namespace AlgebraicTopology.RelativeSimplex

variable {ι : Type v} {R : Type u} [Ring R] {S : Set ι}

/-- Inserting an omitted vertex proves native exactness in each positive degree,
including when the required support is empty. -/
theorem exactAt_succ_of_not_mem (j : ι) (hj : j ∉ S) (n : ℕ) :
    (complex R S).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  change (complex R S).d (n + 1) (n + 2) x = 0 at hx
  refine ⟨prepend j n x, ?_⟩
  funext a
  have h := prepend_d_succ j hj x a
  rw [hx, map_zero] at h
  exact (sub_eq_zero.mp h.symm).symm

/-- Every nonempty tuple in a singleton vertex set has every possible required
support, including full support. -/
theorem supported_of_unique [Unique ι] {n : ℕ} (a : Fin (n + 1) → ι) :
    S ⊆ Set.range a := by
  intro i hi
  exact ⟨0, Subsingleton.elim _ _⟩

instance tupleUnique [Unique ι] (S : Set ι) (n : ℕ) : Unique (Tuple S n) where
  default := ⟨fun _ => default, supported_of_unique _⟩
  uniq _a := Subsingleton.elim _ _

/-- For one vertex the literal extension-by-zero inclusion from full support to
empty support is an isomorphism of the actual native complexes. -/
theorem fullSupportToEmpty_isIso_of_unique [Unique ι] :
    IsIso (complexSupportMap (R := R) (Set.empty_subset (Set.univ : Set ι))) := by
  let f := complexSupportMap (R := R) (Set.empty_subset (Set.univ : Set ι))
  have (n : ℕ) : IsIso (f.f n) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    constructor
    · intro x y hxy
      funext a
      have h := congrFun hxy (⟨a.val, Set.empty_subset _⟩ : Tuple (∅ : Set ι) n)
      change extendByZero x a.val = extendByZero y a.val at h
      simpa only [extendByZero_apply] using h
    · intro y
      refine ⟨fun a => y ⟨a.val, Set.empty_subset _⟩, ?_⟩
      funext a
      change extendByZero (fun b : Tuple (Set.univ : Set ι) n =>
        y ⟨b.val, Set.empty_subset _⟩) a.val = y a
      classical
      simp only [extendByZero, dite_eq_left (supported_of_unique a.val)]
  exact HomologicalComplex.Hom.isIso_of_components f

/-- Native positive homology vanishes when the vertex set has one element. -/
theorem exactAt_succ_of_unique [Unique ι] (n : ℕ) :
    (complex R (Set.univ : Set ι)).ExactAt (n + 1) := by
  let f := complexSupportMap (R := R) (Set.empty_subset (Set.univ : Set ι))
  let := fullSupportToEmpty_isIso_of_unique (R := R) (ι := ι)
  exact (exactAt_succ_of_not_mem (R := R) (S := (∅ : Set ι)) default (by simp) n).of_iso
    (asIso f).symm

/-- The original degree-zero signed deletion differential is zero for one vertex. -/
theorem d_zero_of_unique [Unique ι] :
    (complex R (Set.univ : Set ι)).d 0 1 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext a
  change (complex R (Set.univ : Set ι)).d 0 1 x a = 0
  rw [d_apply, Fin.sum_univ_two]
  have he : a.val ∘ (0 : Fin 2).succAbove = a.val ∘ (1 : Fin 2).succAbove :=
    Subsingleton.elim _ _
  rw [he]
  simp

/-- The native degree-zero homology for one vertex is the scalar module, through
the original cycles inclusion and evaluation on the unique tuple. -/
def homologyZeroLinearEquivOfUnique [Unique ι] :
    (complex R (Set.univ : Set ι)).homology 0 ≃ₗ[R] R :=
  (((complex R (Set.univ : Set ι)).isoHomologyπ₀).symm ≪≫
    (complex R (Set.univ : Set ι)).iCyclesIso 0 1 (by simp)
      d_zero_of_unique).toLinearEquiv.trans (LinearEquiv.funUnique _ R R)

/-- Deprecated compatibility name for `homologyZeroLinearEquivOfUnique`. -/
-- Preserve the public data name as a transparent alias of the canonical construction.
@[deprecated (since := "2026-10-17"), nolint defsWithUnderscore]
alias homologyZeroLinearEquiv_of_unique := homologyZeroLinearEquivOfUnique

end AlgebraicTopology.RelativeSimplex
