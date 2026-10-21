/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.OriginalModel
public import Mathlib.FieldTheory.Normal.Closure

/-! Descent from the literal normal-closure normalization to the original algebra. -/

@[expose] public section

noncomputable section

namespace Algebra

variable (A B K E Ω : Type*) [CommRing A] [IsDomain A]
  [CommRing B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
  [Algebra B E] [IsFractionRing B E] [IsScalarTower A B E]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]
  [Field Ω] [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [Normal K Ω]
  [Nonempty (E →ₐ[K] Ω)]

/-- If the normalization in the actual normal closure is etale, so is the
original finite normal algebra. The splitting condition is supplied by the
normal-closure construction, not an additional hypothesis. -/
theorem etale_of_normalClosure_normalization
    [Etale A (integralClosure A (IntermediateField.normalClosure K E Ω))] : Etale A B :=
  etale_of_splitting_normalization A B K (IntermediateField.normalClosure K E Ω) E
    (fun x => (inferInstance :
      IsNormalClosure K E (IntermediateField.normalClosure K E Ω)).splits x)

end Algebra
