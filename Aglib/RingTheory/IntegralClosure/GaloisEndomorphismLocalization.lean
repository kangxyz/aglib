/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.GaloisEndomorphismGeneric
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# Localization of the original Galois endomorphism map

The native localized map, using coefficient inclusion and extension of
endomorphisms, agrees with the field Galois equivalence. Finite presentation
is used only to identify the endomorphism module with its localization.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace IsIntegralClosure

variable (A K L B : Type*) [CommRing A] [IsDomain A] [Field K] [Field L] [CommRing B]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra A B] [Algebra B L]
  [IsScalarTower A B L] [IsIntegralClosure B A L]
  [FiniteDimensional K L] [IsGalois K L] [Fintype (L ≃ₐ[K] L)]

omit [FiniteDimensional K L] [Fintype (L ≃ₐ[K] L)] in
include K in
/-- The actual normalization inclusion realizes localization at nonzero base elements. -/
theorem fractionInclusion_isLocalizedModule :
    IsLocalizedModule A⁰ (IsScalarTower.toAlgHom A B L).toLinearMap := by
  let : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization A K L B
  infer_instance

/-- The original inclusion applied coordinatewise to Galois coefficients. -/
def galoisCoefficientInclusion : ((L ≃ₐ[K] L) → B) →ₗ[A] ((L ≃ₐ[K] L) → L) :=
  LinearMap.pi fun g => (IsScalarTower.toAlgHom A B L).toLinearMap ∘ₗ LinearMap.proj g

/-- The native extension of base-linear endomorphisms to the fraction field. -/
def galoisEndomorphismInclusion : Module.End A B →ₗ[A] Module.End K L :=
  let := fractionInclusion_isLocalizedModule A K L B
  IsLocalizedModule.mapExtendScalars A⁰
    (IsScalarTower.toAlgHom A B L).toLinearMap
    (IsScalarTower.toAlgHom A B L).toLinearMap K

omit [Fintype (L ≃ₐ[K] L)] in
instance : IsLocalizedModule A⁰ (galoisCoefficientInclusion A K L B) := by
  let := fractionInclusion_isLocalizedModule A K L B
  exact IsLocalizedModule.pi A⁰ _

instance [Module.FinitePresentation A B] :
    IsLocalizedModule A⁰ (galoisEndomorphismInclusion A K L B) := by
  let := fractionInclusion_isLocalizedModule A K L B
  exact Module.FinitePresentation.isLocalizedModule_mapExtendScalars _ _ _ _

/-- Extension of the actual normalization endomorphism equals the field map. -/
theorem galoisEndomorphismInclusion_comp :
    (galoisEndomorphismInclusion A K L B).comp
        ((galoisEndomorphism A K L B).restrictScalars A) =
      ((IsGalois.endomorphismEquiv K L).toLinearMap.restrictScalars A).comp
        (galoisCoefficientInclusion A K L B) := by
  let := fractionInclusion_isLocalizedModule A K L B
  apply LinearMap.ext
  intro c
  apply LinearMap.restrictScalars_injective A
  apply IsLocalizedModule.linearMap_ext A⁰ (IsScalarTower.toAlgHom A B L).toLinearMap
    (IsScalarTower.toAlgHom A B L).toLinearMap
  ext x
  change IsLocalizedModule.map A⁰ (IsScalarTower.toAlgHom A B L).toLinearMap
      (IsScalarTower.toAlgHom A B L).toLinearMap
      (galoisEndomorphism A K L B c)
      ((IsScalarTower.toAlgHom A B L).toLinearMap x) = _
  rw [IsLocalizedModule.map_apply]
  exact (galoisEndomorphism_generic_apply A K L B c x).symm

/-- The native localized coefficient map is the original field equivalence. -/
theorem galoisEndomorphism_localized_eq [Module.FinitePresentation A B] :
    IsLocalizedModule.map A⁰ (galoisCoefficientInclusion A K L B)
        (galoisEndomorphismInclusion A K L B)
        ((galoisEndomorphism A K L B).restrictScalars A) =
      (IsGalois.endomorphismEquiv K L).toLinearMap.restrictScalars A := by
  apply IsLocalizedModule.linearMap_ext A⁰ (galoisCoefficientInclusion A K L B)
    (galoisEndomorphismInclusion A K L B)
  rw [IsLocalizedModule.map_comp]
  exact galoisEndomorphismInclusion_comp A K L B

/-- Bijectivity of the actual generic localization, for reflexive reconstruction. -/
theorem galoisEndomorphism_localized_bijective [Module.FinitePresentation A B] :
    Function.Bijective (IsLocalizedModule.map A⁰ (galoisCoefficientInclusion A K L B)
      (galoisEndomorphismInclusion A K L B)
      ((galoisEndomorphism A K L B).restrictScalars A)) := by
  rw [galoisEndomorphism_localized_eq]
  exact (IsGalois.endomorphismEquiv K L).bijective

end IsIntegralClosure
