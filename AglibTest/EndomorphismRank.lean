/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.Algebra.Module.EndomorphismRank

universe u v w x i j k

example (R : Type u) [CommRing R] [IsDomain R]
    (M : Type v) [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.IsTorsionFree R M] [Nontrivial M]
    (ι : Type i) [Fintype ι] (e : (M →ₗ[R] M) ≃ₗ[R] (ι → M)) :
    Module.finrank R M = Fintype.card ι :=
  Module.finrank_eq_card_of_end_equiv_pi e

example (R : Type u) [CommRing R] [IsDomain R]
    (M : Type v) [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.IsTorsionFree R M] [Nontrivial M]
    (P₁ : Type w) [AddCommGroup P₁] [Module R P₁]
    (P₀ : Type x) [AddCommGroup P₀] [Module R P₀]
    (ι : Type i) [Fintype ι] (e : (M →ₗ[R] M) ≃ₗ[R] (ι → M))
    (ι₁ : Type j) [Fintype ι₁] (ι₀ : Type k) [Fintype ι₀]
    (b₁ : Module.Basis ι₁ R P₁) (b₀ : Module.Basis ι₀ R P₀)
    (f : P₁ →ₗ[R] P₀) (g : P₀ →ₗ[R] M)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) :
    Fintype.card ι₀ = Fintype.card ι₁ + Fintype.card ι :=
  Module.basis_card_eq_add_card_of_end_equiv_pi e b₁ b₀ f g hf hg hex
