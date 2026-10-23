/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Brauer.C1Splitting
public import Aglib.FieldTheory.Tsen.AlgebraicFunctionField

/-!
# Central simple algebras over algebraic function-field extensions

No finite-degree hypothesis on the extension of the rational function field is
needed. Finite coefficient descent supplies C₁, and the actual central-simple
splitting theorem applies to every finite-dimensional central simple algebra.
-/

@[expose] public noncomputable section

universe u v

variable (K : Type*) [Field K] [IsAlgClosed K]
variable (E : Type u) [Field E] [Algebra (RatFunc K) E]
  [Algebra.IsAlgebraic (RatFunc K) E]

include K

/-- Actual matrix splitting over any algebraic extension of an algebraically
closed rational function field. -/
theorem CSA.exists_matrix_of_algebraic_ratFunc (A : CSA.{u, v} E) :
    ∃ (n : ℕ) (_ : NeZero n), Nonempty (A ≃ₐ[E] Matrix (Fin n) (Fin n) E) := by
  let : Infinite E := Infinite.of_injective
    (fun x : K => algebraMap (RatFunc K) E (algebraMap K (RatFunc K) x))
    ((algebraMap (RatFunc K) E).injective.comp (algebraMap K (RatFunc K)).injective)
  exact CSA.exists_matrix_of_isC1 (Field.isC1_algebraic_ratFunc K E) A

/-- The native Brauer quotient is a singleton even for an infinite-degree
algebraic extension of the rational function field. -/
theorem BrauerGroup.subsingleton_of_algebraic_ratFunc :
    Subsingleton (BrauerGroup.{u, u} E) := by
  let : Infinite E := Infinite.of_injective
    (fun x : K => algebraMap (RatFunc K) E (algebraMap K (RatFunc K) x))
    ((algebraMap (RatFunc K) E).injective.comp (algebraMap K (RatFunc K)).injective)
  exact BrauerGroup.subsingleton_of_isC1 E (Field.isC1_algebraic_ratFunc K E)
