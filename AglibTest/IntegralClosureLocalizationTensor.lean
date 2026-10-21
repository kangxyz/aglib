module

import Aglib.RingTheory.IntegralClosure.LocalizationTensor

open scoped TensorProduct

noncomputable section

variable (A D L : Type*) [CommRing A] [CommRing D] [CommRing L]
  [Algebra A D] [Algebra D L] [Algebra A L] [IsScalarTower A D L]
  (M : Submonoid A) [IsLocalization M D]

example (d : D) (b : integralClosure A L) :
    (integralClosure.scalarExtensionTensorEquiv A D L M (d ⊗ₜ[A] b) : L) =
      algebraMap D L d * (b : L) :=
  integralClosure.scalarExtensionTensorEquiv_tmul A D L M d b
