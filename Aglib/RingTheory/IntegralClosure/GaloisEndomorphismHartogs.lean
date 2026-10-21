/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.GaloisEndomorphismLocalization
public import Aglib.RingTheory.IntegralClosure.Reflexive
public import Aglib.RingTheory.Reflexive.Pi
public import Aglib.RingTheory.Reflexive.HeightOneReconstruction

/-!
# Reconstructing the original Galois coefficient map from height one

Reflexivity of the actual finite normalization and its coefficient module is
derived, not assumed. The original generic map is the Galois field equivalence.
Only surjectivity of the canonical local maps at height-one primes remains as
an explicit local input; the local etale supplier provides that input.
-/

@[expose] public section

noncomputable section

namespace IsIntegralClosure

variable (A K L B : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
  [IsIntegrallyClosed A] [Field K] [Field L] [CommRing B]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra A B] [Algebra B L]
  [IsScalarTower A B L] [IsIntegralClosure B A L]
  [FiniteDimensional K L] [IsGalois K L] [Fintype (L ≃ₐ[K] L)]

/-- Height-one local surjectivity reconstructs every original base-linear
endomorphism with integral Galois coefficients. -/
theorem galoisEndomorphism_surjective_of_localized_height_one
    (hloc : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
      Function.Surjective (LocalizedModule.map p.primeCompl
        ((galoisEndomorphism A K L B).restrictScalars A))) :
    Function.Surjective (galoisEndomorphism A K L B) := by
  let : Module.Finite A B := IsIntegralClosure.finite A K L B
  let := Module.finitePresentation_of_finite A B
  let := Module.finitePresentation_of_finite A ((L ≃ₐ[K] L) → B)
  let := Module.finitePresentation_of_finite A (Module.Dual A ((L ≃ₐ[K] L) → B))
  let : Module.IsReflexive A B := IsIntegralClosure.isReflexive A K L B
  exact LinearMap.surjective_of_generic_bijective_of_localized_height_one (K := K)
    ((galoisEndomorphism A K L B).restrictScalars A)
    (galoisCoefficientInclusion A K L B) (galoisEndomorphismInclusion A K L B)
    (galoisEndomorphism_localized_bijective A K L B) hloc

/-- The reconstructed map is an equivalence of coefficient modules, with its
original forward map unchanged. -/
def galoisEndomorphismEquivOfLocalizedHeightOne
    (hloc : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
      Function.Surjective (LocalizedModule.map p.primeCompl
        ((galoisEndomorphism A K L B).restrictScalars A))) :
    ((L ≃ₐ[K] L) → B) ≃ₗ[B] Module.End A B :=
  LinearEquiv.ofBijective (galoisEndomorphism A K L B)
    ⟨galoisEndomorphism_injective A K L B,
      galoisEndomorphism_surjective_of_localized_height_one A K L B hloc⟩

end IsIntegralClosure
