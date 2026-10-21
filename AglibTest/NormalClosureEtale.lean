module

import Aglib.RingTheory.IntegralClosure.Inertia.NormalClosure

open scoped TensorProduct

noncomputable section

variable (R K Ω E : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω] [IsGalois K Ω]
  [Field E] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]
  [Algebra E Ω] [IsScalarTower K E Ω]
  [Algebra.Etale R (integralClosure R E)]

example (Q : Ideal (integralClosure R Ω)) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    Algebra.Etale R (integralClosure R (IntermediateField.normalClosure K E Ω)) := by
  let : Module.Finite R (integralClosure R E) := IsIntegralClosure.finite R K E _
  exact integralClosure.Inertia.normalClosure_etale_of_finiteEtaleModel
    R K Ω (integralClosure R E) E (integralClosure.genericFiberEquiv R K E) Q
