/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.RingTheory.IntegralClosure.GaloisEndomorphism

/-! The Galois endomorphism map on the literal integral closure. -/

noncomputable section

variable (A K L : Type*) [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra.IsAlgebraic K L] [Fintype (L ≃ₐ[K] L)]

example : Function.Injective
    (IsIntegralClosure.galoisEndomorphism A K L (integralClosure A L)) :=
  IsIntegralClosure.galoisEndomorphism_injective A K L (integralClosure A L)

example (c : (L ≃ₐ[K] L) → integralClosure A L) (x : integralClosure A L) :
    algebraMap (integralClosure A L) L
        (IsIntegralClosure.galoisEndomorphism A K L (integralClosure A L) c x) =
      ∑ g, algebraMap (integralClosure A L) L (c g) *
        g (algebraMap (integralClosure A L) L x) :=
  IsIntegralClosure.algebraMap_galoisEndomorphism_apply A K L (integralClosure A L) c x
