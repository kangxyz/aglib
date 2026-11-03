/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethOpenMayerVietoris.RestrictionLinearAlgebra

/-! # Naturality with the original whole maps in the conclusion -/

@[expose] public section

open scoped DirectSum

universe r i a b c d

namespace DirectSum

/-- Use the original generator laws to retain the actual whole maps in the square. -/
theorem linearMap_naturality_of_components {R : Type r} [Semiring R]
    {ι : Type i} [DecidableEq ι] {A : ι → Type a} {B : ι → Type b}
    [∀ s, AddCommMonoid (A s)] [∀ s, Module R (A s)]
    [∀ s, AddCommMonoid (B s)] [∀ s, Module R (B s)]
    {P : Type c} {Q : Type d} [AddCommMonoid P] [Module R P]
    [AddCommMonoid Q] [Module R Q]
    (F : (⨁ s, A s) →ₗ[R] ⨁ s, B s)
    (K : (⨁ s, A s) →ₗ[R] P) (L : (⨁ s, B s) →ₗ[R] Q) (g : P →ₗ[R] Q)
    {f : ∀ s, A s →ₗ[R] B s} {φ : ∀ s, A s →ₗ[R] P} {ψ : ∀ s, B s →ₗ[R] Q}
    (h : ∀ s, ψ s ∘ₗ f s = g ∘ₗ φ s)
    (hF : ∀ s x, F (lof R ι A s x) = lof R ι B s (f s x))
    (hK : ∀ s x, K (lof R ι A s x) = φ s x)
    (hL : ∀ s x, L (lof R ι B s x) = ψ s x) :
    L.comp F = g.comp K := by
  have hFeq : F = lmap f := by
    apply linearMap_ext
    intro s
    apply LinearMap.ext
    intro x
    exact (hF s x).trans (lmap_lof f s x).symm
  have hKeq : K = toModule R ι P φ := by
    apply linearMap_ext
    intro s
    apply LinearMap.ext
    intro x
    exact (hK s x).trans (toModule_lof (φ := φ) R s x).symm
  have hLeq : L = toModule R ι Q ψ := by
    apply linearMap_ext
    intro s
    apply LinearMap.ext
    intro x
    exact (hL s x).trans (toModule_lof (φ := ψ) R s x).symm
  rw [hFeq, hKeq, hLeq]
  exact toModule_naturality_of_components φ ψ g h

end DirectSum
