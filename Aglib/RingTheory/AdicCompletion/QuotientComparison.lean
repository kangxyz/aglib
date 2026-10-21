/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Reductions of the native adic completion

For a finitely generated ideal, evaluation identifies each reduction of the
completed module with the original reduction. All maps and transition equations
are those of the native ideal-power quotients.
-/

@[expose] public section

noncomputable section

namespace AdicCompletion

variable {R : Type*} [CommRing R] (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M]

/-- Reduction of a completion is the original reduction, via evaluation. -/
def quotientEquiv (hI : I.FG) (n : ℕ) :
    (AdicCompletion I M ⧸ (I ^ n • ⊤ : Submodule R (AdicCompletion I M))) ≃ₗ[R]
      (M ⧸ (I ^ n • ⊤ : Submodule R M)) :=
  (Submodule.quotEquivOfEq _ _ (pow_smul_top_eq_ker_eval (M := M) hI)) ≪≫ₗ
    (eval I M n).quotKerEquivOfSurjective (eval_surjective I M n)

@[simp]
theorem quotientEquiv_mk (hI : I.FG) (n : ℕ) (x : AdicCompletion I M) :
    quotientEquiv I M hI n (Submodule.Quotient.mk x) = eval I M n x := rfl

@[simp]
theorem quotientEquiv_mk_of (hI : I.FG) (n : ℕ) (x : M) :
    quotientEquiv I M hI n (Submodule.Quotient.mk (of I M x)) =
      Submodule.Quotient.mk x := rfl

/-- The evaluation identifications commute with the native quotient transitions. -/
theorem quotientEquiv_factorPow (hI : I.FG) {m n : ℕ} (h : m ≤ n) :
    (quotientEquiv I M hI m).toLinearMap ∘ₗ
        Submodule.factorPow I (AdicCompletion I M) h =
      Submodule.factorPow I M h ∘ₗ (quotientEquiv I M hI n).toLinearMap := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact (transitionMap_comp_eval_apply I M h x).symm

end AdicCompletion
