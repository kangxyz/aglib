/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AssociatedGraded.Components

/-! # Original homogeneous multiplication and degree-zero scalars -/

@[expose] public noncomputable section

open Polynomial
universe u
namespace Ideal
variable {A : Type u} [CommRing A] (I : Ideal A)

/-- Homogeneous multiplication is induced by multiplication of the original
ideal-power coefficients. -/
lemma associatedGradedComponentMap_mul (r n : ℕ)
    (a : ↥(I ^ r : Ideal A)) (b : ↥(I ^ n : Ideal A)) :
    (I.associatedGradedComponentMap r a : I.associatedGraded) *
        (I.associatedGradedComponentMap n b : I.associatedGraded) =
      (I.associatedGradedComponentMap (r + n)
        ⟨(a : A) * (b : A), by
          rw [pow_add]
          exact Ideal.mul_mem_mul a.property b.property⟩ : I.associatedGraded) := by
  simp only [associatedGradedComponentMap_coe, ← map_mul]
  congr 1
  apply Subtype.ext
  exact Polynomial.monomial_mul_monomial _ _ _ _

/-- Degree-zero coefficients act through the original structural algebra map. -/
lemma associatedGradedComponentMap_zero (a : A) :
    (I.associatedGradedComponentMap 0 ⟨a, by simp⟩ : I.associatedGraded) =
      algebraMap A I.associatedGraded a := by
  rw [I.associatedGradedComponentMap_coe]
  have he : (reesAlgebra.homogeneous I 0 ⟨a, by simp⟩ : reesAlgebra I) =
      algebraMap A (reesAlgebra I) a := by
    apply Subtype.ext
    exact Polynomial.monomial_zero_left (a := a)
  rw [he, Ideal.Quotient.mk_algebraMap]

end Ideal
