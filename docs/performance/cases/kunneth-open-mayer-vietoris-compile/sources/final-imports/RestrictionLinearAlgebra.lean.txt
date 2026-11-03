/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.DirectSum.Module

/-! # Whole naturality at the original direct-sum component maps -/

@[expose] public section

universe r i a b c d

namespace DirectSum

/-- Assemble the whole coproduct square using the component arrows inferred from its equations. -/
theorem toModule_naturality_of_components {R : Type r} [Semiring R]
    {ι : Type i} [DecidableEq ι] {A : ι → Type a} {B : ι → Type b}
    [∀ s, AddCommMonoid (A s)] [∀ s, Module R (A s)]
    [∀ s, AddCommMonoid (B s)] [∀ s, Module R (B s)]
    {P : Type c} {Q : Type d} [AddCommMonoid P] [Module R P]
    [AddCommMonoid Q] [Module R Q]
    (φ : ∀ s, A s →ₗ[R] P) (ψ : ∀ s, B s →ₗ[R] Q) (g : P →ₗ[R] Q)
    {f : ∀ s, A s →ₗ[R] B s}
    (h : ∀ s, ψ s ∘ₗ f s = g ∘ₗ φ s) :
    (toModule R ι Q ψ).comp (lmap f) = g.comp (toModule R ι P φ) := by
  apply linearMap_ext
  intro s
  apply LinearMap.ext
  intro x
  have hValue := LinearMap.congr_fun (h s) x
  simpa only [LinearMap.comp_apply, lmap_lof, toModule_lof] using hValue

end DirectSum
