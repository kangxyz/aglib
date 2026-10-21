/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.FieldTheory.Separable.TensorProductSplitting

/-! The field splitting map, including its actual normal-field specialization. -/

noncomputable section

open scoped TensorProduct

variable (K E L : Type*) [Field K] [Field E] [Field L] [Algebra K E] [Algebra K L]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]

example (hsplit : ∀ x : E, ((minpoly K x).map (algebraMap K L)).Splits)
    (a : L) (x : E) (σ : E →ₐ[K] L) :
    Algebra.IsSeparable.tensorProductEquivPi K E L hsplit (a ⊗ₜ[K] x) σ = a * σ x :=
  Algebra.IsSeparable.tensorProductEquivPi_tmul K E L hsplit a x σ

example [Algebra E L] [IsScalarTower K E L] [Normal K L] :
    Function.Bijective (Algebra.IsSeparable.tensorProductEvaluation K E L) := by
  apply Algebra.IsSeparable.tensorProductEvaluation_bijective K E L
  intro x
  rw [← minpoly.algHom_eq (IsScalarTower.toAlgHom K E L)
    (IsScalarTower.toAlgHom K E L).injective x]
  exact Normal.splits (inferInstance : Normal K L) _
