/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Brauer.C1Splitting
public import Aglib.FieldTheory.Tsen.FiniteFunctionField

/-!
# Central simple algebras over finite function fields

Tsen's polynomial theorem and the constructed reduced-norm argument give actual
matrix splittings over every finite extension of `K(t)` for algebraically closed
`K`. This is an algebraic Brauer result, not an étale-cohomology comparison.
-/

@[expose] public noncomputable section

universe u v

variable (K : Type*) [Field K] [IsAlgClosed K]
variable (E : Type u) [Field E] [Algebra (RatFunc K) E]
  [FiniteDimensional (RatFunc K) E]

private theorem infinite_functionField (K E : Type*) [Field K] [IsAlgClosed K]
    [Field E] [Algebra (RatFunc K) E] : Infinite E :=
  Infinite.of_injective (fun x : K => algebraMap (RatFunc K) E (algebraMap K (RatFunc K) x))
    ((algebraMap (RatFunc K) E).injective.comp (algebraMap K (RatFunc K)).injective)

include K

/-- A central simple algebra over a finite extension of an algebraically closed
rational function field is an actual matrix algebra over its coefficient field. -/
theorem CSA.exists_matrix_of_finite_ratFunc (A : CSA.{u, v} E) :
    ∃ (n : ℕ) (_ : NeZero n), Nonempty (A ≃ₐ[E] Matrix (Fin n) (Fin n) E) := by
  let := infinite_functionField K E
  exact CSA.exists_matrix_of_isC1 (Field.isC1_finite_ratFunc K E) A

/-- The original native Brauer quotient of a finite function field is a singleton. -/
theorem BrauerGroup.subsingleton_of_finite_ratFunc :
    Subsingleton (BrauerGroup.{u, u} E) := by
  let := infinite_functionField K E
  exact BrauerGroup.subsingleton_of_isC1 E (Field.isC1_finite_ratFunc K E)
