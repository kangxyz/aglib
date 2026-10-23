/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.RationalCoefficientRoot
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Algebraic.Integral

/-! # Rational evaluation after an algebraic extension of constants -/

@[expose] public noncomputable section

open scoped RatFunc
attribute [local instance] Polynomial.algebra

namespace RatFunc

variable (k K L : Type*) [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L]
  [Algebra.IsAlgebraic k K]

/-- The original rational variable stays transcendental after algebraic extension
of the constant field. -/
theorem transcendental_variable_of_algebraic_constants :
    Transcendental K (algebraMap (RatFunc k) L RatFunc.X) := by
  apply (Algebra.IsAlgebraic.transcendental_iff k K).mp
  exact (transcendental_algebraMap_iff (algebraMap (RatFunc k) L).injective).mpr
    RatFunc.transcendental_X

/-- The actual rational-function map induced by the extended constants and the
original rational variable. -/
def algebraicConstantsEvaluation : RatFunc K →ₐ[K] L :=
  (IntermediateField.adjoin K {algebraMap (RatFunc k) L RatFunc.X}).val.comp
    (RatFunc.algEquivOfTranscendental _
      (transcendental_variable_of_algebraic_constants k K L)).toAlgHom

@[simp] theorem algebraicConstantsEvaluation_C (a : K) :
    algebraicConstantsEvaluation k K L (RatFunc.C a) = algebraMap K L a :=
  (algebraicConstantsEvaluation k K L).commutes a

@[simp] theorem algebraicConstantsEvaluation_X :
    algebraicConstantsEvaluation k K L RatFunc.X = algebraMap (RatFunc k) L RatFunc.X := by
  exact RatFunc.algEquivOfTranscendental_X _ _

/-- The rational evaluation map agrees with the supplied original field map,
not just with an abstract isomorphic rational-function subfield. -/
theorem algebraicConstantsEvaluation_comp :
    (algebraicConstantsEvaluation k K L).toRingHom.comp
      (algebraMap (RatFunc k) (RatFunc K)) = algebraMap (RatFunc k) L := by
  rw [Polynomial.LocalResidue.ratFunc_algebraMap_eq_fractionMap]
  apply IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial k))
  apply Polynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, RatFunc.algebraMap_C,
      Polynomial.LocalResidue.fractionMap_C]
    change algebraicConstantsEvaluation k K L (RatFunc.C (algebraMap k K a)) =
      algebraMap (RatFunc k) L (RatFunc.C a)
    rw [algebraicConstantsEvaluation_C]
    change algebraMap K L (algebraMap k K a) =
      algebraMap (RatFunc k) L (algebraMap k (RatFunc k) a)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  · simp only [RingHom.comp_apply, RatFunc.algebraMap_X,
      Polynomial.LocalResidue.fractionMap_X]
    exact algebraicConstantsEvaluation_X k K L

/-- The chosen rational-function algebra retains the exact original rational map. -/
theorem exists_algebraicConstantsAlgebra :
    ∃ a : Algebra (RatFunc K) L,
      letI := a
      (algebraMap (RatFunc K) L).comp (algebraMap (RatFunc k) (RatFunc K)) =
        algebraMap (RatFunc k) L := by
  let a := (algebraicConstantsEvaluation k K L).toRingHom.toAlgebra
  exact ⟨a, algebraicConstantsEvaluation_comp k K L⟩

end RatFunc
