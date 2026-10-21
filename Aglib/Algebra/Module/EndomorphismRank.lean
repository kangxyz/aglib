/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.Algebra.Exact.Basic

/-!
# Rank determined by an endomorphism-module equivalence

Localizing the original equivalence at the fraction field computes its
multiplicity. Nontriviality and torsion-freeness justify cancellation of the
positive generic rank. Rank-nullity then supplies the basis-cardinality relation
for any genuine finite-free presentation.
-/

@[expose] public section

namespace Module

open TensorProduct

variable {R : Type*} [CommRing R] [IsDomain R]
    {M : Type*} [AddCommGroup M] [Module R M]

/-- A finite-presentation torsion-free nonzero module has rank equal to the
multiplicity in an equivalence between its endomorphisms and a finite power. -/
theorem finrank_eq_card_of_end_equiv_pi [FinitePresentation R M]
    [IsTorsionFree R M] [Nontrivial M]
    {ι : Type*} [Fintype ι] (e : (M →ₗ[R] M) ≃ₗ[R] (ι → M)) :
    finrank R M = Fintype.card ι := by
  let K := FractionRing R
  let V := K ⊗[R] M
  let f : M →ₗ[R] V := TensorProduct.mk R K M 1
  let ef : (M →ₗ[R] M) →ₗ[R] (V →ₗ[K] V) :=
    IsLocalizedModule.mapExtendScalars (nonZeroDivisors R) f f K
  let pf : (ι → M) →ₗ[R] (ι → V) := LinearMap.pi fun i ↦ f.comp (LinearMap.proj i)
  let eK : (V →ₗ[K] V) ≃ₗ[K] (ι → V) :=
    IsLocalizedModule.mapEquiv (nonZeroDivisors R) ef pf K e
  have hV : finrank K V = finrank R M := by
    rw [IsFractionRing.finrank_right_eq R K V]
    exact IsLocalizedModule.finrank_eq (nonZeroDivisors R) f le_rfl
  have he := eK.finrank_eq
  rw [finrank_linearMap, finrank_pi_fintype] at he
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hV] at he
  exact (Nat.mul_right_cancel (finrank_pos (R := R) (M := M)) he)

variable {P₁ : Type*} [AddCommGroup P₁] [Module R P₁]
    {P₀ : Type*} [AddCommGroup P₀] [Module R P₀]

/-- Rank-nullity for the actual short exact presentation, expressed using any
chosen finite bases and the original endomorphism-module equivalence. -/
theorem basis_card_eq_add_card_of_end_equiv_pi [FinitePresentation R M]
    [IsTorsionFree R M] [Nontrivial M]
    {ι : Type*} [Fintype ι] (e : (M →ₗ[R] M) ≃ₗ[R] (ι → M))
    {ι₁ : Type*} [Fintype ι₁] {ι₀ : Type*} [Fintype ι₀]
    (b₁ : Basis ι₁ R P₁) (b₀ : Basis ι₀ R P₀)
    (f : P₁ →ₗ[R] P₀) (g : P₀ →ₗ[R] M)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) :
    Fintype.card ι₀ = Fintype.card ι₁ + Fintype.card ι := by
  let : Module.Finite R P₀ := Module.Finite.of_basis b₀
  have h := (LinearMap.ker g).finrank_quotient_add_finrank
  rw [(g.quotKerEquivOfSurjective hg).finrank_eq,
    LinearMap.exact_iff.mp hex, ← (LinearEquiv.ofInjective f hf).finrank_eq,
    finrank_eq_card_basis b₀, finrank_eq_card_basis b₁,
    finrank_eq_card_of_end_equiv_pi e] at h
  exact h.symm.trans (Nat.add_comm _ _)

end Module
