/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The explicit contraction for a proper nonempty relative support

Inserting a vertex outside `S` in the first position contracts the actual
relative-simplex complex when `S` is nonempty. The formulas retain the native
alternating deletion differential and the extension-by-zero convention.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v

namespace AlgebraicTopology.RelativeSimplex

variable {ι : Type v} {R : Type u} [Ring R] {S : Set ι} {n : ℕ}

theorem supported_cons_iff (j : ι) (hj : j ∉ S) (a : Fin (n + 1) → ι) :
    S ⊆ Set.range (Fin.cons j a) ↔ S ⊆ Set.range a := by
  rw [Fin.range_cons]
  constructor
  · intro h i hi
    rcases h hi with hji | hai
    · exact (hj (hji ▸ hi)).elim
    · exact hai
  · exact fun h _ hi => Set.mem_insert_of_mem _ (h hi)

/-- The actual degree-minus-one scalar-linear operator: insert the chosen
vertex at the front of an admissible tuple. -/
def prepend (j : ι) (n : ℕ) : Cochains R S (n + 1) →ₗ[R] Cochains R S n where
  toFun x a := x ⟨Fin.cons j a.val, fun i hi => by
    rw [Fin.range_cons]
    exact Set.mem_insert_of_mem _ (a.property hi)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem extendByZero_prepend (j : ι) (hj : j ∉ S) (x : Cochains R S (n + 1))
    (a : Fin (n + 1) → ι) :
    extendByZero (prepend j n x) a = extendByZero x (Fin.cons j a) := by
  classical
  by_cases ha : S ⊆ Set.range a
  · have hja := (supported_cons_iff j hj a).mpr ha
    simp only [extendByZero, dite_eq_left ha, dite_eq_left hja, prepend,
      LinearMap.coe_mk, AddHom.coe_mk]
  · have hja : ¬ S ⊆ Set.range (Fin.cons j a) :=
      fun h => ha ((supported_cons_iff j hj a).mp h)
    simp only [extendByZero, dite_eq_right ha, dite_eq_right hja]

/-- The displayed differential formula remains valid on every tuple after
extension by zero, including tuples which omit a prescribed vertex. -/
theorem extendByZero_d (x : Cochains R S n) (a : Fin (n + 2) → ι) :
    extendByZero ((complex R S).d n (n + 1) x) a =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        extendByZero x (a ∘ k.succAbove) := by
  classical
  by_cases ha : S ⊆ Set.range a
  · exact (extendByZero_apply _ ⟨a, ha⟩).trans (d_apply x ⟨a, ha⟩)
  · rw [extendByZero_of_not_supported _ _ ha]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    rw [extendByZero_of_not_supported _ _ (fun h => ha (supported_of_comp h)), smul_zero]

/-- The signed deletion identity in every positive degree. -/
theorem prepend_d_succ (j : ι) (hj : j ∉ S) (x : Cochains R S (n + 1))
    (a : Tuple S (n + 1)) :
    prepend j (n + 1) ((complex R S).d (n + 1) (n + 2) x) a =
      x a - (complex R S).d n (n + 1) (prepend j n x) a := by
  change (complex R S).d (n + 1) (n + 2) x
    ⟨Fin.cons j a.val, _⟩ = _
  rw [d_apply, Fin.sum_univ_succ, d_apply]
  have hzero : Fin.cons j a.val ∘ (0 : Fin (n + 3)).succAbove = a.val := by
    funext i
    simp
  rw [hzero, extendByZero_apply]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    Fin.cons_comp_succ_succAbove, ← extendByZero_prepend j hj, pow_succ,
    mul_neg_one, neg_smul]
  rw [Finset.sum_neg_distrib]
  have hface (k : Fin (n + 2)) : k.removeNth a.val = a.val ∘ k.succAbove := by
    funext i
    rfl
  simp only [sub_eq_add_neg, hface]

/-- Nonempty support removes the degree-zero augmentation term in the same
insertion identity. -/
theorem prepend_d_zero (j : ι) (hj : j ∉ S) (hS : S.Nonempty)
    (x : Cochains R S 0) (a : Tuple S 0) :
    prepend j 0 ((complex R S).d 0 1 x) a = x a := by
  change (complex R S).d 0 1 x ⟨Fin.cons j a.val, _⟩ = _
  rw [d_apply, Fin.sum_univ_two]
  have hzero : Fin.cons j a.val ∘ (0 : Fin 2).succAbove = a.val := by
    funext i
    simp
  have hone : Fin.cons j a.val ∘ (1 : Fin 2).succAbove = fun _ => j := by
    funext i
    rw [Fin.eq_zero i]
    rfl
  have hnot : ¬ S ⊆ Set.range (fun _ : Fin 1 => j) := by
    intro h
    obtain ⟨i, hi⟩ := hS
    obtain ⟨k, hk⟩ := h hi
    have hki : j = i := hk
    exact hj (hki.symm ▸ hi)
  rw [hzero, hone, extendByZero_apply, extendByZero_of_not_supported _ _ hnot]
  simp

/-- Components of the native contraction homotopy, with the original insertion
operator on successive degrees and zero elsewhere. -/
def contractionHom (j : ι) (m n : ℕ) : (complex R S).X m ⟶ (complex R S).X n := by
  classical
  exact if h : n + 1 = m then
    eqToHom (congrArg (fun k => (complex R S).X k) h.symm) ≫ ModuleCat.ofHom (prepend j n)
  else 0

@[simp]
theorem contractionHom_succ (j : ι) (n : ℕ) :
    contractionHom (R := R) (S := S) j (n + 1) n = ModuleCat.ofHom (prepend j n) := by
  simp [contractionHom]

/-- The identity of the actual native complex is null-homotopic when the
required support is nonempty and omits the chosen vertex. -/
def contraction (j : ι) (hj : j ∉ S) (hS : S.Nonempty) :
    Homotopy (𝟙 (complex R S)) 0 where
  hom := contractionHom j
  zero m n h := by
    classical
    dsimp [contractionHom]
    rw [dite_eq_right]
    exact fun hmn => h (by dsimp; omega)
  comm n := by
    cases n with
    | zero =>
      rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_zero_cochainComplex]
      simp only [contractionHom_succ, HomologicalComplex.id_f, HomologicalComplex.zero_f,
        add_zero]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply funext
      intro a
      exact (prepend_d_zero j hj hS x a).symm
    | succ n =>
      rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex]
      simp only [contractionHom_succ, HomologicalComplex.id_f, HomologicalComplex.zero_f,
        add_zero]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply funext
      intro a
      change x a = prepend j (n + 1) ((complex R S).d (n + 1) (n + 2) x) a +
        (complex R S).d n (n + 1) (prepend j n x) a
      rw [prepend_d_succ j hj]
      abel

/-- Every actual homology object vanishes for proper nonempty support. -/
theorem acyclic_of_nonempty_of_not_mem (j : ι) (hj : j ∉ S) (hS : S.Nonempty) :
    (complex R S).Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  have h := (contraction (R := R) j hj hS).homologyMap_eq n
  simpa only [homologyMap_id, homologyMap_zero] using h

end AlgebraicTopology.RelativeSimplex
