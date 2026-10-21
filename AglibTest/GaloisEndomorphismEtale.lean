/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.RingTheory.IntegralClosure.GaloisEndomorphismEtale

/-! Tests on the literal integral closure, including the canonical inverse law. -/

noncomputable section

variable (A K L : Type*) [CommRing A] [IsNoetherianRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L]
  [Fintype (L ≃ₐ[K] L)]
  [Module.Free A (integralClosure A L)] [Module.Finite A (integralClosure A L)]
  [Algebra.Etale A (integralClosure A L)]

example : Function.Bijective
    (IsIntegralClosure.galoisEndomorphism A K L (integralClosure A L)) :=
  IsIntegralClosure.galoisEndomorphism_bijective_of_etale A K L (integralClosure A L)

example (f : Module.End A (integralClosure A L)) :
    IsIntegralClosure.galoisEndomorphism A K L (integralClosure A L)
      ((IsIntegralClosure.galoisEndomorphismEquivOfEtale A K L
        (integralClosure A L)).symm f) = f :=
  (IsIntegralClosure.galoisEndomorphismEquivOfEtale A K L
    (integralClosure A L)).apply_symm_apply f
