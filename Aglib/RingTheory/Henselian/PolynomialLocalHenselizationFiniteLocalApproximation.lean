/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationFiniteApproximation
public import Aglib.RingTheory.AdicCompletion.FiniteLocalCofinality
public import Mathlib.RingTheory.Ideal.GoingUp

/-! # Arbitrary-ideal approximation in finite local polynomial-origin algebras

The extended-maximal-ideal completion is compared with the actual maximal-ideal
completion by the proved Artinian closed-fibre power bound. Exact solvability
there is then passed to arbitrary proper ideals by affine substitution.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial

namespace PolynomialLocalHenselization

universe u v w
variable (k : Type u) [Field k] (n : ℕ)
local notation "H" => PolynomialLocalHenselization k n

/-- Every proper ideal in a finite local algebra over the actual polynomial-origin
henselization admits approximation. No approximation premise remains. -/
theorem exists_solution_finite_local_ideal_completion_with_precision
    (A : Type u) [CommRing A] [Algebra H A] [Module.Finite H A]
    [IsLocalRing A]
    (I : Ideal A) (hI : I ≠ ⊤)
    {σ : Type v} {ι : Type w} [Finite σ] [Finite ι]
    (F : ι → MvPolynomial σ A) (y : σ → AdicCompletion I A)
    (hy : ∀ i, eval₂ (algebraMap A (AdicCompletion I A)) y (F i) = 0) (c : ℕ) :
    ∃ x : σ → A,
      (∀ i, eval x (F i) = 0) ∧
      (∀ j, Ideal.Quotient.mk (I ^ c) (x j) = AdicCompletion.evalₐ I c (y j)) ∧
      ∀ j, algebraMap A (AdicCompletion I A) (x j) - y j ∈
        (I ^ c).map (algebraMap A (AdicCompletion I A)) := by
  let : IsLocalHom (algebraMap H A) :=
    ((local_hom_TFAE (algebraMap H A)).out 5 1).mp
      (eq_maximalIdeal (show ((maximalIdeal A).comap (algebraMap H A)).IsMaximal from
        inferInstance))
  let : IsNoetherianRing H := Henselization.isNoetherianRing (PolynomialLocalRing k n)
  let : IsNoetherianRing A := IsNoetherianRing.of_finite H A
  apply AdicCompletion.exists_solution_of_larger_ideal_solver I (maximalIdeal A)
    (le_maximalIdeal hI) (IsNoetherian.noetherian I) ?_ F y hy c
  intro τ _ E t ht
  let e := AdicCompletion.finiteLocalAlgEquiv (R := H) (A := A)
  let t' := fun j ↦ e.symm (t j)
  have ht' (i : ι) : eval₂
      (algebraMap A (AdicCompletion ((maximalIdeal H).map (algebraMap H A)) A))
      t' (E i) = 0 := by
    have h := congrArg e.symm.toRingHom (ht i)
    rw [hom_eval₂, map_zero] at h
    have hc : e.symm.toRingHom.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) =
        algebraMap A (AdicCompletion ((maximalIdeal H).map (algebraMap H A)) A) := by
      apply RingHom.ext
      intro a
      exact e.symm.commutes a
    rw [hc] at h
    exact h
  obtain ⟨b, hb, _⟩ := exists_solution_finite_algebra_completion_with_precision k n A
    (maximalIdeal H) (maximalIdeal.isMaximal H).ne_top E t' ht' 0
  exact ⟨b, hb⟩

end PolynomialLocalHenselization
