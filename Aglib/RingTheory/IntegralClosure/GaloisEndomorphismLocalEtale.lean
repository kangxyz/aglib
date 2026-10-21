/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.GaloisEndomorphismBaseChange
public import Aglib.RingTheory.IntegralClosure.Localization
public import Aglib.RingTheory.IntegralClosure.FiniteEtale

/-!
# Local Galois surjectivity for literal normalizations

This specializes the actual coefficient-map localization theorem to literal
integral closures over a normal Noetherian domain and its DVR localization.
The localization map is the same-element scalar-extension inclusion, not an
assumed abstract comparison. Etaleness of the DVR normalization remains an
explicit hypothesis, to be supplied by the normal-closure inertia theorem.
-/

@[expose] public section

noncomputable section

namespace integralClosure

variable (A K L D : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
  [IsIntegrallyClosed A] [Field K] [Field L] [CommRing D] [IsDomain D]
  [IsDiscreteValuationRing D] [Algebra A D]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra D K] [IsFractionRing D K]
  [Algebra D L] [IsScalarTower D K L] [IsScalarTower A D L]
  [FiniteDimensional K L] [IsGalois K L] [Fintype (L ≃ₐ[K] L)]
  (M : Submonoid A) [IsLocalization M D]

/-- Etaleness of the literal DVR normalization gives surjectivity of the
canonical localized global coefficient map. -/
theorem galoisEndomorphism_localized_surjective_of_etale
    [Algebra.Etale D (integralClosure D L)] :
    Function.Surjective (LocalizedModule.map M
      ((IsIntegralClosure.galoisEndomorphism A K L (integralClosure A L)).restrictScalars A)) := by
  let := scalarExtensionAlgebra A D L
  let := scalarExtension_isScalarTower_base A D L
  let := scalarExtension_isScalarTower_ambient A D L
  let := scalarExtension_isLocalization A D L M
  let : Module.Finite A (integralClosure A L) := IsIntegralClosure.finite A K L _
  let := Module.finitePresentation_of_finite A (integralClosure A L)
  let : Module.Finite D (integralClosure D L) := IsIntegralClosure.finite D K L _
  let : Module.IsTorsionFree D L := .trans_faithfulSMul D K L
  let : Module.Free D (integralClosure D L) := IsIntegralClosure.module_free D K L _
  exact IsIntegralClosure.galoisEndomorphism_localizedModule_surjective_of_etale
    A K L (integralClosure A L) D (integralClosure D L) M

end integralClosure
