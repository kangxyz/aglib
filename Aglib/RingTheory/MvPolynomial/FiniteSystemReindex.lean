/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.RingTheory.Ideal.Operations

/-! # Finite polynomial systems from a Fin-indexed solver

This is only reindexing. The solver is an explicit hypothesis, not an
approximation instance. Equation and unknown index types are independent.
-/

@[expose] public section

noncomputable section

universe u v w uσ uι

namespace MvPolynomial

/-- A solver for all `Fin`-indexed systems handles arbitrary independent finite
index types, without changing either coefficient map or the requested precision. -/
theorem exists_finite_solution_of_fin_solver
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (τ : B →+* C) (I : Ideal C)
    (hsolve : ∀ (s t : ℕ) (F : Fin t → MvPolynomial (Fin s) A)
      (y : Fin s → C),
      (∀ i, eval₂ (τ.comp φ) y (F i) = 0) →
      ∀ c : ℕ, ∃ x : Fin s → B,
        (∀ i, eval₂ φ x (F i) = 0) ∧ ∀ j, τ (x j) - y j ∈ I ^ c)
    {σ : Type uσ} {ι : Type uι} [Finite σ] [Finite ι]
    (F : ι → MvPolynomial σ A) (y : σ → C)
    (hy : ∀ i, eval₂ (τ.comp φ) y (F i) = 0) (c : ℕ) :
    ∃ x : σ → B,
      (∀ i, eval₂ φ x (F i) = 0) ∧ ∀ j, τ (x j) - y j ∈ I ^ c := by
  classical
  let := Fintype.ofFinite σ
  let := Fintype.ofFinite ι
  let eσ := Fintype.equivFin σ
  let eι := Fintype.equivFin ι
  let G : Fin (Fintype.card ι) → MvPolynomial (Fin (Fintype.card σ)) A :=
    fun i => rename eσ (F (eι.symm i))
  let z : Fin (Fintype.card σ) → C := fun j => y (eσ.symm j)
  have hz : ∀ i, eval₂ (τ.comp φ) z (G i) = 0 := by
    intro i
    simpa only [G, z, eval₂_rename, Function.comp_def, Equiv.symm_apply_apply] using
      hy (eι.symm i)
  obtain ⟨x, hx, hclose⟩ := hsolve _ _ G z hz c
  refine ⟨fun j => x (eσ j), ?_, ?_⟩
  · intro i
    simpa only [G, eval₂_rename, Function.comp_def, Equiv.symm_apply_apply] using
      hx (eι i)
  · intro j
    simpa only [z, Equiv.symm_apply_apply] using hclose (eσ j)

end MvPolynomial
