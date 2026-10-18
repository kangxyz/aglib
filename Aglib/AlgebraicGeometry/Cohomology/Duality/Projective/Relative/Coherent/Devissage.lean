/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.FiveLemma

/-!
# Uniform coefficient dévissage

The degree induction first proves injectivity for every coefficient, then uses
that uniform injectivity at the quotient coefficient to prove surjectivity.
The map on the cover term may include a unit sign; the original maps on the
coefficient and quotient remain fixed.
-/

@[expose] public section

namespace AddMonoidHom

universe u v w

variable {I : Type u} {A : I → ℕ → Type v} {B : I → ℕ → Type w}
  [∀ i q, AddCommGroup (A i q)] [∀ i q, AddCommGroup (B i q)]
  (φ : ∀ i q, A i q →+ B i q)

/-- A coefficient cover sequence, its exact rows, and its original comparison ladder.
Only the cover comparison is allowed to be rescaled. -/
structure CoefficientDevissageSequence (N C Q : I) where
  /-- The degreewise map from the coefficient term to the cover in the `A`-row. -/
  a₁ : ∀ q, A N q →+ A C q
  /-- The degreewise map from the cover to the quotient in the `A`-row. -/
  a₂ : ∀ q, A C q →+ A Q q
  /-- The connecting map from `A Q q` to `A N (q + 1)`. -/
  aδ : ∀ q, A Q q →+ A N (q + 1)
  /-- The degreewise map from the coefficient term to the cover in the `B`-row. -/
  b₁ : ∀ q, B N q →+ B C q
  /-- The degreewise map from the cover to the quotient in the `B`-row. -/
  b₂ : ∀ q, B C q →+ B Q q
  /-- The connecting map from `B Q q` to `B N (q + 1)`. -/
  bδ : ∀ q, B Q q →+ B N (q + 1)
  /-- The degreewise comparison between the two cover terms. -/
  coverMap : ∀ q, A C q →+ B C q
  cover_bijective : ∀ q, Function.Bijective (coverMap q)
  comm₁ : ∀ q, (b₁ q).comp (φ N q) = (coverMap q).comp (a₁ q)
  comm₂ : ∀ q, (b₂ q).comp (coverMap q) = (φ Q q).comp (a₂ q)
  commδ : ∀ q, (bδ q).comp (φ Q q) = (φ N (q + 1)).comp (aδ q)
  exact_a₂ : ∀ q, Function.Exact (a₁ q) (a₂ q)
  exact_a₃ : ∀ q, Function.Exact (a₂ q) (aδ q)
  exact_a₁ : ∀ q, Function.Exact (aδ q) (a₁ (q + 1))
  exact_b₂ : ∀ q, Function.Exact (b₁ q) (b₂ q)
  exact_b₃ : ∀ q, Function.Exact (b₂ q) (bδ q)
  exact_b₁ : ∀ q, Function.Exact (bδ q) (b₁ (q + 1))
  injective_a₁_zero : Function.Injective (a₁ 0)
  injective_b₁_zero : Function.Injective (b₁ 0)

/-- Covers with bijective comparison imply bijectivity for every coefficient and degree.
In each degree injectivity is obtained uniformly before surjectivity. -/
theorem bijective_of_coefficient_devissage
    (h : ∀ N, ∃ C Q, Nonempty (CoefficientDevissageSequence φ N C Q)) :
    ∀ q N, Function.Bijective (φ N q) := by
  intro q
  induction q with
  | zero =>
    have hmono : ∀ N, Function.Injective (φ N 0) := by
      intro N
      obtain ⟨C, Q, ⟨s⟩⟩ := h N
      intro x y hxy
      apply s.injective_a₁_zero
      apply (s.cover_bijective 0).injective
      exact (DFunLike.congr_fun (s.comm₁ 0) x).symm.trans
        ((congrArg (s.b₁ 0) hxy).trans (DFunLike.congr_fun (s.comm₁ 0) y))
    intro N
    obtain ⟨C, Q, ⟨s⟩⟩ := h N
    exact bijective_of_bijective_of_injective_of_left_exact
      (s.a₁ 0) (s.a₂ 0) (s.b₁ 0) (s.b₂ 0)
      (φ N 0) (s.coverMap 0) (φ Q 0)
      (s.comm₁ 0) (s.comm₂ 0) (s.exact_a₂ 0) (s.exact_b₂ 0)
      (s.cover_bijective 0) (hmono Q) s.injective_a₁_zero s.injective_b₁_zero
  | succ q ih =>
    have hmono : ∀ N, Function.Injective (φ N (q + 1)) := by
      intro N
      obtain ⟨C, Q, ⟨s⟩⟩ := h N
      exact injective_of_surjective_of_injective_of_injective
        (s.a₂ q) (s.aδ q) (s.a₁ (q + 1))
        (s.b₂ q) (s.bδ q) (s.b₁ (q + 1))
        (s.coverMap q) (φ Q q) (φ N (q + 1)) (s.coverMap (q + 1))
        (s.comm₂ q) (s.commδ q) (s.comm₁ (q + 1))
        (s.exact_a₃ q) (s.exact_a₁ q) (s.exact_b₃ q)
        (s.cover_bijective q).surjective (ih Q).injective
        (s.cover_bijective (q + 1)).injective
    intro N
    obtain ⟨C, Q, ⟨s⟩⟩ := h N
    refine ⟨hmono N, ?_⟩
    exact surjective_of_surjective_of_surjective_of_injective
      (s.aδ q) (s.a₁ (q + 1)) (s.a₂ (q + 1))
      (s.bδ q) (s.b₁ (q + 1)) (s.b₂ (q + 1))
      (φ Q q) (φ N (q + 1)) (s.coverMap (q + 1)) (φ Q (q + 1))
      (s.commδ q) (s.comm₁ (q + 1)) (s.comm₂ (q + 1))
      (s.exact_a₂ (q + 1)) (s.exact_b₁ q) (s.exact_b₂ (q + 1))
      (ih Q).surjective (s.cover_bijective (q + 1)).surjective (hmono Q)

end AddMonoidHom
