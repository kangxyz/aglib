module

import Aglib.RingTheory.IntegralClosure.NormalClosureDescent
import Mathlib.FieldTheory.IsSepClosed

noncomputable section

variable (A B K E : Type*) [CommRing A] [IsDomain A]
  [CommRing B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
  [Algebra B E] [IsFractionRing B E] [IsScalarTower A B E]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]
  [Algebra A (SeparableClosure K)] [IsScalarTower A K (SeparableClosure K)]
  [Algebra.Etale A
    (integralClosure A (IntermediateField.normalClosure K E (SeparableClosure K)))]

example : Algebra.Etale A B := by
  let : Nonempty (E →ₐ[K] SeparableClosure K) := ⟨IsSepClosed.lift⟩
  exact Algebra.etale_of_normalClosure_normalization A B K E (SeparableClosure K)
