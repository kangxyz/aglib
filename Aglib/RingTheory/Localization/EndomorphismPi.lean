/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# Localizing an endomorphism-module decomposition

A specified equivalence between the endomorphism module and a finite product
of the original module localizes to the same equivalence over the localized
base. Hom and product comparison maps are the actual native localization maps.
-/

@[expose] public section

noncomputable section

namespace Module.End

variable {R M Mₛ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Mₛ] [Module R Mₛ]
  (S : Submonoid R) (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
  [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
  (j : M →ₗ[R] Mₛ) [IsLocalizedModule S j] [Module.FinitePresentation R M]
  {ι : Type*} [Finite ι]

/-- A finite-product decomposition of the actual endomorphism module persists
under localization, using finite-presentation Hom localization. -/
def localizedEquivPi (e : Module.End R M ≃ₗ[R] (ι → M)) :
    Module.End Rₛ Mₛ ≃ₗ[Rₛ] (ι → Mₛ) := by
  let jEnd : Module.End R M →ₗ[R] Module.End Rₛ Mₛ :=
    IsLocalizedModule.mapExtendScalars S j j Rₛ
  let jPi : (ι → M) →ₗ[R] (ι → Mₛ) := LinearMap.pi fun i ↦ j ∘ₗ LinearMap.proj i
  let : IsLocalizedModule S jPi := IsLocalizedModule.pi S fun _ ↦ j
  exact (IsLocalizedModule.linearEquiv S jEnd (jPi ∘ₗ e.toLinearMap)).extendScalarsOfIsLocalization
    S Rₛ

/-- The localized equivalence commutes with the original endomorphism extension
and coordinatewise module localization. -/
@[simp] theorem localizedEquivPi_apply_mapExtendScalars
    (e : Module.End R M ≃ₗ[R] (ι → M)) (f : Module.End R M) (i : ι) :
    localizedEquivPi S Rₛ j e (IsLocalizedModule.mapExtendScalars S j j Rₛ f) i =
      j (e f i) := by
  simp [localizedEquivPi]

end Module.End
