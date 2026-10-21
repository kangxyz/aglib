/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.Powers
public import Aglib.RingTheory.AdicCompletion.Congruence
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.Tactic.Ring

/-! # Transfer of finite-system approximation to a smaller ideal

Affine substitution enforces the desired ideal congruence by exact equations.
No injectivity of the comparison between the two completions is required.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace AdicCompletion

universe u v w
variable {R : Type u} [CommRing R]

/-- Exact solvability over the larger-ideal completion implies approximation over
any smaller finitely generated ideal. The solvability premise is explicit here;
applications must supply it from an independently proved approximation theorem. -/
theorem exists_solution_of_larger_ideal_solver
    (I J : Ideal R) (hIJ : I ≤ J) (hI : I.FG)
    {σ : Type v} {ι : Type w} [Finite σ]
    (hsolve : ∀ {τ : Type v} [Finite τ] (E : ι → MvPolynomial τ R)
      (z : τ → AdicCompletion J R),
      (∀ i, eval₂ (algebraMap R (AdicCompletion J R)) z (E i) = 0) →
      ∃ w : τ → R, ∀ i, MvPolynomial.eval w (E i) = 0)
    (F : ι → MvPolynomial σ R) (y : σ → AdicCompletion I R)
    (hy : ∀ i, eval₂ (algebraMap R (AdicCompletion I R)) y (F i) = 0) (c : ℕ) :
    ∃ x : σ → R,
      (∀ i, MvPolynomial.eval x (F i) = 0) ∧
      (∀ j, Ideal.Quotient.mk (I ^ c) (x j) = evalₐ I c (y j)) ∧
      ∀ j, algebraMap R (AdicCompletion I R) (x j) - y j ∈
        (I ^ c).map (algebraMap R (AdicCompletion I R)) := by
  classical
  let A := AdicCompletion I R
  let B := AdicCompletion J R
  let f : A →ₐ[R] B := reindexAlgHom I J id monotone_id
    (fun n => pow_le_pow_left' hIJ n)
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (hI.pow (n := c))
  have hg' : Ideal.span (Set.range g) = I ^ c := hg
  choose y0 hy0 using fun j => Ideal.Quotient.mk_surjective (evalₐ I c (y j))
  have hmem (j : σ) : y j - algebraMap R A (y0 j) ∈
      (I ^ c).map (algebraMap R A) := by
    apply (evalₐ_eq_iff_sub_mem I hI c _ _).mp
    change evalₐ I c (y j) = evalₐ I c (AdicCompletion.of I R (y0 j))
    rw [evalₐ_of]
    exact (hy0 j).symm
  have hspan : (I ^ c).map (algebraMap R A) =
      Ideal.span (Set.range (fun l => algebraMap R A (g l))) := by
    rw [← hg', Ideal.map_span, ← Set.range_comp']
  have hzexists (j : σ) : ∃ z : Fin r → A,
      ∑ l, z l * algebraMap R A (g l) = y j - algebraMap R A (y0 j) := by
    apply Ideal.mem_span_range_iff_exists_fun.mp
    rw [← hspan]
    exact hmem j
  choose z hz using hzexists
  let P : σ → MvPolynomial (σ × Fin r) R := fun j =>
    C (y0 j) + ∑ l, X (j, l) * C (g l)
  let t : σ × Fin r → A := fun a => z a.1 a.2
  have hP (j : σ) : eval₂ (algebraMap R A) t (P j) = y j := by
    simp only [P, eval₂_add, eval₂_C, eval₂_sum, eval₂_mul, eval₂_X, t]
    rw [hz j]
    ring
  let E : ι → MvPolynomial (σ × Fin r) R := fun i => bind₁ P (F i)
  have hE (i : ι) : eval₂ (algebraMap R A) t (E i) = 0 := by
    change eval₂Hom (algebraMap R A) t (bind₁ P (F i)) = 0
    rw [eval₂Hom_bind₁]
    simpa only [coe_eval₂Hom, hP] using hy i
  have hE' (i : ι) : eval₂ (algebraMap R B) (fun a => f (t a)) (E i) = 0 := by
    have h := congrArg f.toRingHom (hE i)
    rw [hom_eval₂, _root_.map_zero] at h
    have hc : f.toRingHom.comp (algebraMap R A) = algebraMap R B := by
      apply RingHom.ext
      intro a
      exact f.commutes a
    rw [hc] at h
    exact h
  obtain ⟨w, hw⟩ := hsolve E (fun a => f (t a)) hE'
  let x : σ → R := fun j => MvPolynomial.eval w (P j)
  have hx (i : ι) : MvPolynomial.eval x (F i) = 0 := by
    have h := hw i
    change eval₂Hom (RingHom.id R) w (bind₁ P (F i)) = 0 at h
    rw [eval₂Hom_bind₁] at h
    exact h
  have hx0 (j : σ) : x j - y0 j ∈ I ^ c := by
    have hgmem (l : Fin r) : g l ∈ I ^ c := by
      rw [← hg']
      exact Ideal.subset_span ⟨l, rfl⟩
    have hxeq : x j - y0 j = ∑ l, w (j, l) * g l := by
      simp only [x, P, eval_add, eval_C, eval_sum, eval_mul, eval_X]
      ring
    rw [hxeq]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hgmem l)
  have hprec (j : σ) : algebraMap R A (x j) - y j ∈
      (I ^ c).map (algebraMap R A) := by
    have hm := Ideal.mem_map_of_mem (algebraMap R A) (hx0 j)
    have hs := Ideal.sub_mem ((I ^ c).map (algebraMap R A)) hm (hmem j)
    simpa only [map_sub, sub_sub_sub_cancel_right] using hs
  refine ⟨x, hx, ?_, hprec⟩
  intro j
  have h := (evalₐ_eq_iff_sub_mem I hI c _ _).mpr (hprec j)
  change evalₐ I c (AdicCompletion.of I R (x j)) = _ at h
  rwa [evalₐ_of] at h

end AdicCompletion
