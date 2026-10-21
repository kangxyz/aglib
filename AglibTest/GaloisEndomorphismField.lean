/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Aglib.RingTheory.IntegralClosure.GaloisEndomorphismGeneric

/-! The field equivalence and its compatibility with the literal normalization. -/

noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [Fintype (L ≃ₐ[K] L)]

example (f : Module.End K L) :
    IsGalois.endomorphismEquiv K L ((IsGalois.endomorphismEquiv K L).symm f) = f :=
  (IsGalois.endomorphismEquiv K L).apply_symm_apply f

variable (A : Type*) [CommRing A] [Algebra A K] [IsFractionRing A K]
  [Algebra A L] [IsScalarTower A K L]

example (c : (L ≃ₐ[K] L) → integralClosure A L) (x : integralClosure A L) :
    IsGalois.endomorphismEquiv K L
        (fun g => algebraMap (integralClosure A L) L (c g))
        (algebraMap (integralClosure A L) L x) =
      algebraMap (integralClosure A L) L
        (IsIntegralClosure.galoisEndomorphism A K L (integralClosure A L) c x) :=
  IsIntegralClosure.galoisEndomorphism_generic_apply A K L (integralClosure A L) c x
