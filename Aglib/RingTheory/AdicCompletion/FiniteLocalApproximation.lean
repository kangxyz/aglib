/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.FiniteAlgebraApproximation
public import Aglib.RingTheory.AdicCompletion.FiniteLocalCofinality
public import Aglib.RingTheory.AdicCompletion.ApproximationTransfer
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Approximation transfer to finite local algebras

Approximation in the maximal-ideal completion of a Noetherian local base ring
passes to every proper-ideal completion of a finite local algebra. The actual
finite-algebra comparison, closed-fibre cofinality and affine-substitution
transfer are the existing constructions. The base solver remains an explicit
input of this reusable transfer theorem; applications discharge it with a
proved approximation theorem. The two coefficient rings share one universe.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial

namespace AdicCompletion

universe u v w

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R A] [IsLocalRing A]

/-- A proved maximal-adic base solver supplies arbitrary-ideal approximation in
a finite local algebra, with its original quotient and completion precision. -/
theorem exists_solution_finite_local_of_solver
    (I : Ideal A) (hI : I ≠ ⊤)
    {σ : Type v} {ι : Type w} [Finite σ] [Finite ι]
    (hsolve : ∀ {τ : Type (max v w)} [Finite τ] {ε : Type w} [Finite ε]
      (E : ε → MvPolynomial τ R) (t : τ → AdicCompletion (maximalIdeal R) R),
      (∀ i, eval₂ (algebraMap R (AdicCompletion (maximalIdeal R) R)) t (E i) = 0) →
      ∀ c : ℕ, ∃ b : τ → R, (∀ i, MvPolynomial.eval b (E i) = 0) ∧
        ∀ j, Ideal.Quotient.mk (maximalIdeal R ^ c) (b j) =
          evalₐ (maximalIdeal R) c (t j))
    (F : ι → MvPolynomial σ A) (y : σ → AdicCompletion I A)
    (hy : ∀ i, eval₂ (algebraMap A (AdicCompletion I A)) y (F i) = 0) (c : ℕ) :
    ∃ x : σ → A,
      (∀ i, MvPolynomial.eval x (F i) = 0) ∧
      (∀ j, Ideal.Quotient.mk (I ^ c) (x j) = evalₐ I c (y j)) ∧
      ∀ j, algebraMap A (AdicCompletion I A) (x j) - y j ∈
        (I ^ c).map (algebraMap A (AdicCompletion I A)) := by
  let : IsLocalHom (algebraMap R A) :=
    ((local_hom_TFAE (algebraMap R A)).out 5 1).mp
      (eq_maximalIdeal (show ((maximalIdeal A).comap (algebraMap R A)).IsMaximal from
        inferInstance))
  let : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  apply exists_solution_of_larger_ideal_solver I (maximalIdeal A)
    (le_maximalIdeal hI) (IsNoetherian.noetherian I) ?_ F y hy c
  intro τ _ E t ht
  let e := finiteLocalAlgEquiv (R := R) (A := A)
  let t' := fun j ↦ e.symm (t j)
  have ht' (i : ι) : eval₂
      (algebraMap A (AdicCompletion ((maximalIdeal R).map (algebraMap R A)) A))
      t' (E i) = 0 := by
    have h := congrArg e.symm.toRingHom (ht i)
    rw [hom_eval₂, _root_.map_zero] at h
    have hc : e.symm.toRingHom.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) =
        algebraMap A (AdicCompletion ((maximalIdeal R).map (algebraMap R A)) A) := by
      apply RingHom.ext
      intro a
      exact e.symm.commutes a
    rw [hc] at h
    exact h
  obtain ⟨b, hb, _⟩ := exists_solution_finite_algebra_of_solver
    (maximalIdeal R) hsolve E t' ht' 0
  exact ⟨b, hb⟩

end AdicCompletion
