/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.GaloisEndomorphismEtale
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# Localizing the actual Galois coefficient map

The restricted Galois actions commute with an actual localization of integral
closures, because both agree in the common field. Finite-product and Hom
localization identify the native localized coefficient map with the coefficient
map over the localized base. Its etale bijection therefore supplies the native
local-surjectivity hypothesis used in reflexive reconstruction.
-/

@[expose] public section

noncomputable section

namespace IsIntegralClosure

variable (A K L B D S : Type*) [CommRing A] [Field K] [Field L] [CommRing B]
  [CommRing D] [CommRing S]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra A B] [Algebra B L]
  [IsScalarTower A B L] [IsIntegralClosure B A L]
  [Algebra A D] [Algebra D K] [IsFractionRing D K] [Algebra D L]
  [IsScalarTower D K L] [Algebra D S] [Algebra S L]
  [IsScalarTower D S L] [IsIntegralClosure S D L]
  [Algebra B S] [IsScalarTower B S L]
  [Algebra A S] [IsScalarTower A B S] [IsScalarTower A D S]
  [FiniteDimensional K L] [IsGalois K L] [Fintype (L ≃ₐ[K] L)]

omit [Algebra A D] [Algebra A S] [IsScalarTower A B S] [IsScalarTower A D S]
  [FiniteDimensional K L] in
/-- The actual coefficient actions commute with the inclusion of integral closures. -/
theorem galoisEndomorphism_algebraMap (c : (L ≃ₐ[K] L) → B) (x : B) :
    algebraMap B S (galoisEndomorphism A K L B c x) =
      galoisEndomorphism D K L S (fun g => algebraMap B S (c g)) (algebraMap B S x) := by
  apply IsIntegralClosure.algebraMap_injective S D L
  rw [← IsScalarTower.algebraMap_apply B S L,
    algebraMap_galoisEndomorphism_apply, algebraMap_galoisEndomorphism_apply]
  simp only [← IsScalarTower.algebraMap_apply B S L]

/-- Coordinatewise original inclusion for Galois coefficients. -/
def galoisCoefficientBaseChange : ((L ≃ₐ[K] L) → B) →ₗ[A] ((L ≃ₐ[K] L) → S) :=
  LinearMap.pi fun g => (IsScalarTower.toAlgHom A B S).toLinearMap ∘ₗ LinearMap.proj g

variable (M : Submonoid A) [IsLocalization M D]
  [IsLocalizedModule M (IsScalarTower.toAlgHom A B S).toLinearMap]

/-- Endomorphism extension along the specified actual localization. -/
def galoisEndomorphismBaseChange : Module.End A B →ₗ[A] Module.End D S :=
  IsLocalizedModule.mapExtendScalars M
    (IsScalarTower.toAlgHom A B S).toLinearMap
    (IsScalarTower.toAlgHom A B S).toLinearMap D

omit [Fintype (L ≃ₐ[K] L)] in
instance : IsLocalizedModule M (galoisCoefficientBaseChange A K L B S) :=
  IsLocalizedModule.pi M _

instance [Module.FinitePresentation A B] :
    IsLocalizedModule M (galoisEndomorphismBaseChange A B D S M) :=
  Module.FinitePresentation.isLocalizedModule_mapExtendScalars _ _ _ _

omit [FiniteDimensional K L] in
/-- The square is between the original coefficient map and its native localization. -/
theorem galoisEndomorphismBaseChange_comp :
    (galoisEndomorphismBaseChange A B D S M).comp
        ((galoisEndomorphism A K L B).restrictScalars A) =
      ((galoisEndomorphism D K L S).restrictScalars A).comp
        (galoisCoefficientBaseChange A K L B S) := by
  apply LinearMap.ext
  intro c
  apply LinearMap.restrictScalars_injective A
  apply IsLocalizedModule.linearMap_ext M (IsScalarTower.toAlgHom A B S).toLinearMap
    (IsScalarTower.toAlgHom A B S).toLinearMap
  ext x
  change IsLocalizedModule.map M (IsScalarTower.toAlgHom A B S).toLinearMap
      (IsScalarTower.toAlgHom A B S).toLinearMap (galoisEndomorphism A K L B c)
      ((IsScalarTower.toAlgHom A B S).toLinearMap x) = _
  rw [IsLocalizedModule.map_apply]
  exact galoisEndomorphism_algebraMap A K L B D S c x

/-- Equality with the actual coefficient map over the localized base. -/
theorem galoisEndomorphism_baseChange_eq [Module.FinitePresentation A B] :
    IsLocalizedModule.map M (galoisCoefficientBaseChange A K L B S)
        (galoisEndomorphismBaseChange A B D S M)
        ((galoisEndomorphism A K L B).restrictScalars A) =
      (galoisEndomorphism D K L S).restrictScalars A := by
  apply IsLocalizedModule.linearMap_ext M (galoisCoefficientBaseChange A K L B S)
    (galoisEndomorphismBaseChange A B D S M)
  rw [IsLocalizedModule.map_comp]
  exact galoisEndomorphismBaseChange_comp A K L B D S M

/-- Etaleness of the actual localized normalization supplies the canonical local
surjectivity premise for reflexive reconstruction, without denominator choices. -/
theorem galoisEndomorphism_localizedModule_surjective_of_etale
    [Module.FinitePresentation A B] [IsNoetherianRing D]
    [Module.Free D S] [Module.Finite D S] [Algebra.Etale D S] :
    Function.Surjective (LocalizedModule.map M
      ((galoisEndomorphism A K L B).restrictScalars A)) := by
  apply (IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective
    (galoisCoefficientBaseChange A K L B S)
    (galoisEndomorphismBaseChange A B D S M)).mp
  rw [galoisEndomorphism_baseChange_eq A K L B D S M]
  exact (galoisEndomorphism_bijective_of_etale D K L S).surjective

end IsIntegralClosure
