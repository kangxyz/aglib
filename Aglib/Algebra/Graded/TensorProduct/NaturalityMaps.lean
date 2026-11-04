/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Graded.TensorProduct.CoherenceInputs

/-! # Naturality at the supplied total maps -/

@[expose] public noncomputable section

open scoped TensorProduct

universe u m n p m' n' p'

namespace DirectSum.NaturalityInputs

variable {R : Type u} [Field R]
  {M : ℕ → Type m} {N : ℕ → Type n} {P : ℕ → Type p}
  {M' : ℕ → Type m'} {N' : ℕ → Type n'} {P' : ℕ → Type p'}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
  [∀ i, AddCommMonoid (M' i)] [∀ i, Module R (M' i)]
  [∀ i, AddCommMonoid (N' i)] [∀ i, Module R (N' i)]
  [∀ i, AddCommMonoid (P' i)] [∀ i, Module R (P' i)]

/-- Identify the supplied total maps with the maps on the given degreewise data. -/
structure MapIdentifications (input : NaturalityInputs (R := R) M N P M' N' P')
    (L : (DirectSum ℕ M ⊗[R] DirectSum ℕ N) →ₗ[R] DirectSum ℕ P)
    (L' : (DirectSum ℕ M' ⊗[R] DirectSum ℕ N') →ₗ[R] DirectSum ℕ P')
    (p : DirectSum ℕ P →ₗ[R] DirectSum ℕ P')
    (f : DirectSum ℕ M →ₗ[R] DirectSum ℕ M') (g : DirectSum ℕ N →ₗ[R] DirectSum ℕ N') :
    Prop where
  /-- The source total external map. -/
  source : L = canonicalTotalCupMap M N P input.cup
  /-- The target total external map. -/
  target : L' = canonicalTotalCupMap M' N' P' input.cup'
  /-- The product pullback. -/
  product : p = lmap input.productPullback
  /-- The left pullback. -/
  left : f = lmap input.leftPullback
  /-- The right pullback. -/
  right : g = lmap input.rightPullback

/-- The original naturality equation on the supplied total maps. -/
theorem diagramOfMapIdentifications {input : NaturalityInputs (R := R) M N P M' N' P'}
    {L : (DirectSum ℕ M ⊗[R] DirectSum ℕ N) →ₗ[R] DirectSum ℕ P}
    {L' : (DirectSum ℕ M' ⊗[R] DirectSum ℕ N') →ₗ[R] DirectSum ℕ P'}
    {p : DirectSum ℕ P →ₗ[R] DirectSum ℕ P'}
    {f : DirectSum ℕ M →ₗ[R] DirectSum ℕ M'} {g : DirectSum ℕ N →ₗ[R] DirectSum ℕ N'}
    (h : input.MapIdentifications L L' p f g) :
    p ∘ₗ L = L' ∘ₗ TensorProduct.map f g :=
  input.diagramWithMaps L L' p f g h.source h.target h.product h.left h.right

end DirectSum.NaturalityInputs
