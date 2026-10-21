/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.RingTheory.IntegralClosure.GaloisEndomorphismLocalization

/-! The actual generic localization of the literal normalization coefficient map. -/

noncomputable section

open scoped nonZeroDivisors

variable (A K L : Type*) [CommRing A] [IsDomain A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L]
  [Fintype (L ≃ₐ[K] L)] [Module.FinitePresentation A (integralClosure A L)]

example : Function.Bijective
    (IsLocalizedModule.map A⁰
      (IsIntegralClosure.galoisCoefficientInclusion A K L (integralClosure A L))
      (IsIntegralClosure.galoisEndomorphismInclusion A K L (integralClosure A L))
      ((IsIntegralClosure.galoisEndomorphism A K L (integralClosure A L)).restrictScalars A)) :=
  IsIntegralClosure.galoisEndomorphism_localized_bijective A K L (integralClosure A L)
