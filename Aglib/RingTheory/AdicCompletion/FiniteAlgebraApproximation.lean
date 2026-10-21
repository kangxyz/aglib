/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Module.FinitePresentationPolynomialSolver
public import Aglib.RingTheory.AdicCompletion.FiniteAlgebra
public import Aglib.RingTheory.AdicCompletion.Congruence
public import Mathlib.RingTheory.Finiteness.Ideal

/-! # Approximation over a finite algebra

This is an explicit transfer theorem: the base-ring approximation premise is
visible. Applications must instantiate it with a proved approximation theorem.
The current tensor-completion comparison requires the two coefficient rings
to inhabit the same universe; this restriction is stated rather than hidden.
-/

@[expose] public noncomputable section

open TensorProduct MvPolynomial Module.FinitePresentation
open scoped BigOperators

namespace AdicCompletion

universe u v w
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable [IsNoetherianRing R] [Module.Finite R A]

/-- Actual finite-algebra transfer, with the original quotient projections and
extended ideal-power error in the native completion. -/
theorem exists_solution_finite_algebra_of_solver
    (I : Ideal R)
    {σ : Type v} {ι : Type w} [Finite σ] [Finite ι]
    (hsolve : ∀ {τ : Type (max v w)} [Finite τ] {ε : Type w} [Finite ε]
      (E : ε → MvPolynomial τ R) (t : τ → AdicCompletion I R),
      (∀ i, eval₂ (algebraMap R (AdicCompletion I R)) t (E i) = 0) →
      ∀ c : ℕ, ∃ b : τ → R, (∀ i, MvPolynomial.eval b (E i) = 0) ∧
        ∀ j, Ideal.Quotient.mk (I ^ c) (b j) = evalₐ I c (t j))
    (F : ι → MvPolynomial σ A)
    (y : σ → AdicCompletion (I.map (algebraMap R A)) A)
    (hy : ∀ i, eval₂ (algebraMap A (AdicCompletion (I.map (algebraMap R A)) A))
      y (F i) = 0) (c : ℕ) :
    ∃ x : σ → A,
      (∀ i, MvPolynomial.eval x (F i) = 0) ∧
      (∀ j, Ideal.Quotient.mk ((I.map (algebraMap R A)) ^ c) (x j) =
        evalₐ (I.map (algebraMap R A)) c (y j)) ∧
      ∀ j, algebraMap A (AdicCompletion (I.map (algebraMap R A)) A) (x j) - y j ∈
        ((I.map (algebraMap R A)) ^ c).map
          (algebraMap A (AdicCompletion (I.map (algebraMap R A)) A)) := by
  classical
  let J := I.map (algebraMap R A)
  let T := AdicCompletion I R
  let U := AdicCompletion J A
  let e : T ⊗[R] A ≃ₐ[R] U := tensorEquivExtendedCompletion I
  let L : T →ₐ[R] U := e.toAlgHom.comp Algebra.TensorProduct.includeLeft
  let K : Ideal T := (I ^ c).map (algebraMap R T)
  let K' : Ideal U := (J ^ c).map (algebraMap A U)
  have hK : K.map L.toRingHom = K' := by
    dsimp [K, K', J]
    rw [Ideal.map_map, ← Ideal.map_pow, Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro r
    exact (L.commutes r).trans (IsScalarTower.algebraMap_apply R A U r)
  let := Module.finitePresentation_of_finite R A
  obtain ⟨d, r, f, g, hf, hgf⟩ := Module.FinitePresentation.exists_fin' R A
  choose z hz using fun j ↦ tensorCoordinates_surjective T f hf (e.symm (y j))
  have hez (j : σ) : e (tensorCoordinates T f (z j)) = y j := by rw [hz, e.apply_symm_apply]
  have hformal (i : ι) : eval₂
      (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom
      (fun j ↦ tensorCoordinates T f (z j)) (F i) = 0 := by
    apply e.injective
    change e.toRingHom (eval₂
      (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom
      (fun j ↦ tensorCoordinates T f (z j)) (F i)) = e.toRingHom 0
    rw [_root_.map_zero, hom_eval₂]
    have hc : e.toRingHom.comp
        (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom =
        algebraMap A U := by
      apply RingHom.ext
      intro a
      exact tensorEquivExtendedCompletion_one_tmul I a
    rw [hc]
    change eval₂ (algebraMap A U) (fun j ↦ e (tensorCoordinates T f (z j))) (F i) = 0
    simpa only [hez] using hy i
  have hsolve' : ∀ {τ : Type (max v w)} [Finite τ] {ε : Type w} [Finite ε]
      (E : ε → MvPolynomial τ R) (t : τ → T),
      (∀ i, eval₂ (algebraMap R T) t (E i) = 0) →
      ∃ b : τ → R, (∀ i, MvPolynomial.eval b (E i) = 0) ∧
        ∀ j, algebraMap R T (b j) - t j ∈ K := by
    intro τ _ ε _ E t ht
    obtain ⟨b, hb, hp⟩ := hsolve E t ht c
    refine ⟨b, hb, fun j ↦ ?_⟩
    apply (evalₐ_eq_iff_sub_mem I (IsNoetherian.noetherian I) c _ _).mp
    change evalₐ I c (AdicCompletion.of I R (b j)) = _
    rw [evalₐ_of]
    exact hp j
  obtain ⟨b, hb, hp⟩ := exists_solution_coordinates_of_solver f hf g hgf K hsolve' F z hformal
  let x : σ → A := fun j ↦ f (b j)
  have hx (j : σ) : algebraMap A U (x j) =
      ∑ a, L (algebraMap R T (b j a)) * algebraMap A U (f (Pi.single a 1)) := by
    dsimp [x]
    rw [presentation_apply]
    simp only [map_sum, Algebra.smul_def, map_mul, L.commutes]
    congr 1
  have hy' (j : σ) : y j =
      ∑ a, L (z j a) * algebraMap A U (f (Pi.single a 1)) := by
    rw [← hez j, tensorCoordinates_apply, map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have hm : z j a ⊗ₜ[R] f (Pi.single a 1) =
        (z j a ⊗ₜ[R] (1 : A)) * (1 ⊗ₜ[R] f (Pi.single a 1)) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [hm, map_mul, tensorEquivExtendedCompletion_one_tmul]
    rfl
  have hprec (j : σ) : algebraMap A U (x j) - y j ∈ K' := by
    rw [hx, hy', ← Finset.sum_sub_distrib]
    apply Ideal.sum_mem
    intro a ha
    rw [← sub_mul, ← map_sub]
    apply Ideal.mul_mem_right
    rw [← hK]
    exact Ideal.mem_map_of_mem L.toRingHom (hp j a)
  refine ⟨x, hb, ?_, hprec⟩
  intro j
  have h := (evalₐ_eq_iff_sub_mem J
    (Ideal.FG.map (IsNoetherian.noetherian I) (algebraMap R A)) c _ _).mpr (hprec j)
  change evalₐ J c (AdicCompletion.of J A (x j)) = _ at h
  rwa [evalₐ_of] at h

end AdicCompletion
