/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.FiniteAlgebraApproximation
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationIdealApproximation

/-! # Artin approximation in finite algebras over a polynomial-origin henselization

The generic finite-algebra transfer is instantiated with the proved
polynomial-origin approximation theorem, over an arbitrary field and any proper
base ideal. There is no approximation oracle in the statement. The coefficient
algebra is finite as a module, not assumed free or flat. The same-universe
restriction is inherited explicitly from the tensor-completion comparison.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace PolynomialLocalHenselization

universe u v w
variable (k : Type u) [Field k] (n : ℕ)
local notation "H" => PolynomialLocalHenselization k n

/-- Approximation in a genuine finite algebra over the actual polynomial-origin
henselization, at the extension of any proper base ideal. -/
theorem exists_solution_finite_algebra_completion_with_precision
    (A : Type u) [CommRing A] [Algebra H A] [Module.Finite H A]
    (I : Ideal H) (hI : I ≠ ⊤)
    {σ : Type v} {ι : Type w} [Finite σ] [Finite ι]
    (F : ι → MvPolynomial σ A)
    (y : σ → AdicCompletion (I.map (algebraMap H A)) A)
    (hy : ∀ i, eval₂ (algebraMap A (AdicCompletion (I.map (algebraMap H A)) A))
      y (F i) = 0) (c : ℕ) :
    ∃ x : σ → A,
      (∀ i, eval x (F i) = 0) ∧
      (∀ j, Ideal.Quotient.mk ((I.map (algebraMap H A)) ^ c) (x j) =
        AdicCompletion.evalₐ (I.map (algebraMap H A)) c (y j)) ∧
      ∀ j, algebraMap A (AdicCompletion (I.map (algebraMap H A)) A) (x j) - y j ∈
        ((I.map (algebraMap H A)) ^ c).map
          (algebraMap A (AdicCompletion (I.map (algebraMap H A)) A)) := by
  let : IsNoetherianRing H := Henselization.isNoetherianRing (PolynomialLocalRing k n)
  apply AdicCompletion.exists_solution_finite_algebra_of_solver I ?_ F y hy c
  intro τ _ ε _ E t ht c
  obtain ⟨b, hb, hp, _⟩ :=
    exists_solution_ideal_completion_with_precision k n I hI E t ht c
  exact ⟨b, hb, hp⟩

end PolynomialLocalHenselization
