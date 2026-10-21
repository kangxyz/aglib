module

import Aglib.RingTheory.IntegralClosure.GenericTensor

open scoped TensorProduct

noncomputable section

variable (A K L E : Type*) [CommRing A] [IsDomain A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra.IsIntegral K L]
  [CommRing E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]

example (c : integralClosure A L) (x : E) :
    integralClosure.genericTensorEquiv A K L E (c ⊗ₜ[A] x) = (c : L) ⊗ₜ[K] x :=
  integralClosure.genericTensorEquiv_tmul A K L E c x
