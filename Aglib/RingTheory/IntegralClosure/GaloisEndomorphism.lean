/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Galois endomorphisms of an integral closure

The coefficient-linear map from copies of an integral closure to its base-linear
endomorphisms sends the coefficient at `g` to multiplication followed by `g`.
It uses the existing `galRestrict` on the actual integral closure. Artin's
independence theorem makes this map injective. No surjectivity, flatness or
purity assertion is made here; the codimension-one comparison is a separate
obligation.
-/

@[expose] public section

noncomputable section

namespace IsIntegralClosure

variable (A K L B : Type*) [CommRing A] [Field K] [Field L] [CommRing B]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra A B] [Algebra B L]
  [IsScalarTower A B L] [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L]
  [Fintype (L ≃ₐ[K] L)]

/-- The actual coefficient-linear Galois endomorphism map on an integral closure. -/
def galoisEndomorphism : ((L ≃ₐ[K] L) → B) →ₗ[B] Module.End A B :=
  Fintype.linearCombination B fun g => (galRestrict A K L B g).toLinearMap

/-- The endomorphism is the sum of multiplication followed by the restricted action. -/
theorem galoisEndomorphism_apply (c : (L ≃ₐ[K] L) → B) (x : B) :
    galoisEndomorphism A K L B c x = ∑ g, c g * galRestrict A K L B g x := by
  simp [galoisEndomorphism, Fintype.linearCombination_apply]

/-- The formula preserves the original inclusion of the integral closure in the field. -/
theorem algebraMap_galoisEndomorphism_apply (c : (L ≃ₐ[K] L) → B) (x : B) :
    algebraMap B L (galoisEndomorphism A K L B c x) =
      ∑ g, algebraMap B L (c g) * g (algebraMap B L x) := by
  simp [galoisEndomorphism_apply, algebraMap_galRestrict_apply]

/-- A single coefficient acts by multiplication followed by the selected automorphism. -/
theorem galoisEndomorphism_single [DecidableEq (L ≃ₐ[K] L)]
    (g : L ≃ₐ[K] L) (c x : B) :
    galoisEndomorphism A K L B (Pi.single g c) x = c * galRestrict A K L B g x := by
  simp [galoisEndomorphism, Fintype.linearCombination_apply_single]

/-- Artin independence proves injectivity without an unramifiedness hypothesis. -/
theorem galoisEndomorphism_injective :
    Function.Injective (galoisEndomorphism A K L B) := by
  let : IsDomain B := (IsIntegralClosure.algebraMap_injective B A L).isDomain
  apply linearIndependent_iff_injective_fintypeLinearCombination.mp
  exact (linearIndependent_algHom_toLinearMap A B B).comp
    (fun g => (galRestrict A K L B g).toAlgHom)
    (AlgEquiv.coe_toAlgHom_injective.comp (galRestrict A K L B).injective)

end IsIntegralClosure
