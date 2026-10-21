/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Galois.Endomorphism
public import Aglib.RingTheory.IntegralClosure.GaloisEndomorphism

/-!
# Compatibility with the Galois field endomorphism equivalence

The coefficient map on the actual integral closure agrees with the finite
Galois field equivalence after applying the original inclusions to coefficients
and arguments. This is the concrete compatibility needed for a subsequent
localized-module comparison; no local torsor or integral surjectivity is asserted.
-/

@[expose] public section

noncomputable section

namespace IsIntegralClosure

variable (A K L B : Type*) [CommRing A] [Field K] [Field L] [CommRing B]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra A B] [Algebra B L]
  [IsScalarTower A B L] [IsIntegralClosure B A L]
  [FiniteDimensional K L] [IsGalois K L] [Fintype (L ≃ₐ[K] L)]

/-- The normalization map and the field equivalence commute on the actual
coefficients and arguments, through the original inclusion into the field. -/
theorem galoisEndomorphism_generic_apply (c : (L ≃ₐ[K] L) → B) (x : B) :
    IsGalois.endomorphismEquiv K L (fun g => algebraMap B L (c g)) (algebraMap B L x) =
      algebraMap B L (galoisEndomorphism A K L B c x) := by
  rw [IsGalois.endomorphismEquiv_apply, algebraMap_galoisEndomorphism_apply]

end IsIntegralClosure
