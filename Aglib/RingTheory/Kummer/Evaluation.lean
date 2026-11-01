/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.RootBaseChange

/-! # Evaluation of the original root algebra

The specified root evaluates the literal quotient with its original coefficient
map. Compatible coefficient changes preserve the whole original evaluation.
-/

@[expose] public noncomputable section

open Polynomial

namespace Algebra.Kummer

universe u v w

section Evaluation

variable (R : Type u) (L : Type w) [CommRing R] [CommRing L] [Algebra R L]
  (N : ℕ) (f : R) (β : L) (hpow : β ^ N = algebraMap R L f)

/-- Evaluation of the original polynomial quotient at the specified root. -/
def rootEvaluation : RootAlgebra N f →ₐ[R] L :=
  AdjoinRoot.liftAlgHom (rootPolynomial N f) (Algebra.ofId R L) β (by simp [hpow])

/-- The field action retains the actual original root-evaluation map. -/
@[instance_reducible] def rootEvaluationAlgebra : Algebra (RootAlgebra N f) L :=
  (rootEvaluation R L N f β hpow).toRingHom.toAlgebra

@[simp] theorem rootEvaluation_root :
    rootEvaluation R L N f β hpow (AdjoinRoot.root (rootPolynomial N f)) = β :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

end Evaluation

section BaseChange

variable (R B L : Type*) [CommRing R] [CommRing B] [CommRing L]
  [Algebra R B] [Algebra R L] [Algebra B L] [IsScalarTower R B L]
  (N : ℕ) (f : R) (β : L) (hpow : β ^ N = algebraMap R L f)
  (hpowB : β ^ N = algebraMap B L (algebraMap R B f))

/-- The whole evaluation triangle retains the original coefficient-change root map. -/
theorem rootEvaluation_baseChange :
    ((rootEvaluation B L N (algebraMap R B f) β hpowB).restrictScalars R).comp
      (rootBaseChangeHom B N f) = rootEvaluation R L N f β hpow := by
  apply AdjoinRoot.algHom_ext
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    rootBaseChangeHom_root, rootEvaluation_root]

end BaseChange

end Algebra.Kummer
