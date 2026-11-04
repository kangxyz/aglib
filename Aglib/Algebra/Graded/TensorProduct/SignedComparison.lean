/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Graded.TensorProduct
public import Aglib.Algebra.Graded.ExternalProduct

/-!
# The original signed and chosen total comparisons

All comparisons use the supplied graded algebra data and original maps.
The scalar-parent comparisons are made over variable graded families, before
specializing to coherent cohomology. No new source equivalence or inverse is chosen.
-/

@[expose] public noncomputable section

open scoped TensorProduct DirectSum

universe r i a c m n p

namespace DirectSum

/-- The original coproduct operator after its original inclusion is its component map. -/
theorem toModule_comp_lof_eq {R : Type r} [Semiring R] {ι : Type i} [DecidableEq ι]
    {A : ι → Type a} [∀ j, AddCommMonoid (A j)] [∀ j, Module R (A j)]
    {C : Type c} [AddCommMonoid C] [Module R C]
    (f : ∀ j, A j →ₗ[R] C) (j : ι) :
    (toModule R ι C f).comp (lof R ι A j) = f j := by
  apply LinearMap.ext
  intro x
  exact toModule_lof (φ := f) R j x

section Signed

variable {R : Type r} [CommRing R]
  {M : ℕ → Type m} {N : ℕ → Type n} {P : ℕ → Type p}
  [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]
  [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]
  [∀ j, AddCommGroup (P j)] [∀ j, Module R (P j)]
  [GRing M] [GAlgebra R M] [GRing N] [GAlgebra R N] [GRing P] [GAlgebra R P]
  [gradeM : GradedAlgebra (summandSubmodule (R := R) M)]
  [gradeN : GradedAlgebra (summandSubmodule (R := R) N)]

/-- The literal whole-map equality on the original signed source and supplied total operator. -/
def ExternalSignedTotalEq
    (Φ : GradedTensorProduct R (summandSubmodule (R := R) M)
      (summandSubmodule (R := R) N) →ₐ[R] DirectSum ℕ P)
    (s : (DirectSum ℕ M ⊗[R] DirectSum ℕ N) ≃ₗ[R]
      GradedTensorProduct R (summandSubmodule (R := R) M) (summandSubmodule (R := R) N))
    (L : (DirectSum ℕ M ⊗[R] DirectSum ℕ N) →ₗ[R] DirectSum ℕ P) : Prop :=
  Φ.toLinearMap ∘ₗ s.toLinearMap = L

/-- The three original homogeneous value laws give the complete signed comparison. -/
theorem externalSignedTotalEq_of_values
    (Φ : GradedTensorProduct R (summandSubmodule (R := R) M)
      (summandSubmodule (R := R) N) →ₐ[R] DirectSum ℕ P)
    (s : (DirectSum ℕ M ⊗[R] DirectSum ℕ N) ≃ₗ[R]
      GradedTensorProduct R (summandSubmodule (R := R) M) (summandSubmodule (R := R) N))
    (L : (DirectSum ℕ M ⊗[R] DirectSum ℕ N) →ₗ[R] DirectSum ℕ P)
    (e : ∀ j l, M j → N l → P (j + l))
    (hs : ∀ a b, s (a ⊗ₜ[R] b) = a ᵍ⊗ₜ[R] b)
    (hΦ : ∀ j l x y,
      Φ (homogeneousInclusion (R := R) M j x ᵍ⊗ₜ[R]
        homogeneousInclusion (R := R) N l y) =
      homogeneousInclusion (R := R) P (j + l) (e j l x y))
    (hL : ∀ j l x y,
      L (homogeneousInclusion (R := R) M j x ⊗ₜ[R]
        homogeneousInclusion (R := R) N l y) =
      homogeneousInclusion (R := R) P (j + l) (e j l x y)) :
    ExternalSignedTotalEq Φ s L := by
  unfold ExternalSignedTotalEq
  apply tensorDirectSum_ext M N
  intro j l x y
  have hSource := congrArg Φ
    (hs (homogeneousInclusion (R := R) M j x) (homogeneousInclusion (R := R) N l y))
  exact hSource.trans ((hΦ j l x y).trans (hL j l x y).symm)

/-- The same chosen forward equivalence inherits the original signed comparison. -/
theorem ExternalSignedTotalEq.of_chosen
    {Φ : GradedTensorProduct R (summandSubmodule (R := R) M)
      (summandSubmodule (R := R) N) →ₐ[R] DirectSum ℕ P}
    {s : (DirectSum ℕ M ⊗[R] DirectSum ℕ N) ≃ₗ[R]
      GradedTensorProduct R (summandSubmodule (R := R) M) (summandSubmodule (R := R) N)}
    {L : (DirectSum ℕ M ⊗[R] DirectSum ℕ N) →ₗ[R] DirectSum ℕ P}
    (h : ExternalSignedTotalEq Φ s L)
    (C : (DirectSum ℕ M ⊗[R] DirectSum ℕ N) ≃ₗ[R] DirectSum ℕ P)
    (hC : C.toLinearMap = L) : ExternalSignedTotalEq Φ s C.toLinearMap := by
  unfold ExternalSignedTotalEq at h ⊢
  exact h.trans hC.symm

end Signed

end DirectSum
