/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Reflexive.QuotientEndomorphism
public import Aglib.RingTheory.Localization.QuotSMulTop
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.Module

/-! Actual endomorphism reduction commutes with localization and is locally surjective
where the original localized module is projective. -/

@[expose] public section

noncomputable section

namespace QuotSMulTop

variable {R Rₛ M Mₛ : Type*} [CommRing R] [CommRing Rₛ] [Algebra R Rₛ]
  [AddCommGroup M] [Module R M] [AddCommGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ]
  [IsScalarTower R Rₛ Mₛ] (S : Submonoid R) [IsLocalization S Rₛ]
  (j : M →ₗ[R] Mₛ) [IsLocalizedModule S j] (a : R)

/-- The quotient action of an original endomorphism agrees with the action of its actual
localized endomorphism. -/
theorem map_localization_compatibility (f : Module.End R M) :
    IsLocalizedModule.mapExtendScalars S
      (localizationMap (Rₛ := Rₛ) S j a) (localizationMap (Rₛ := Rₛ) S j a) Rₛ
      (QuotSMulTop.map a f) =
    QuotSMulTop.map (algebraMap R Rₛ a) (IsLocalizedModule.mapExtendScalars S j j Rₛ f) := by
  let jU := localizationMap (Rₛ := Rₛ) S j a
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.linearMap_ext S jU jU
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change IsLocalizedModule.map S jU jU (QuotSMulTop.map a f)
      (jU (Submodule.Quotient.mk x)) =
    QuotSMulTop.map (algebraMap R Rₛ a) (IsLocalizedModule.mapExtendScalars S j j Rₛ f)
      (jU (Submodule.Quotient.mk x))
  rw [IsLocalizedModule.map_apply, map_apply_mk]
  change Submodule.Quotient.mk (j (f x)) =
    Submodule.Quotient.mk (IsLocalizedModule.map S j j f (j x))
  rw [IsLocalizedModule.map_apply]

include Rₛ j in
/-- The actual localized quotient-action map is surjective wherever the localized original
module is projective. Only finite-presentation Hom localization is used. -/
theorem localized_map_surjective_of_projective
    [Module.FinitePresentation R M] [Module.FinitePresentation R (QuotSMulTop a M)]
    [Module.Projective Rₛ Mₛ] :
    Function.Surjective (LocalizedModule.map S
      (QuotSMulTop.map a : Module.End R M →ₗ[R] Module.End R (QuotSMulTop a M))) := by
  let jU := localizationMap (Rₛ := Rₛ) S j a
  let jE := IsLocalizedModule.mapExtendScalars S j j Rₛ
  let jF := IsLocalizedModule.mapExtendScalars S jU jU Rₛ
  let a' := algebraMap R Rₛ a
  have hmap : IsLocalizedModule.map S jE jF (QuotSMulTop.map a) =
      (QuotSMulTop.map a' : Module.End Rₛ Mₛ →ₗ[Rₛ]
        Module.End Rₛ (QuotSMulTop a' Mₛ)).restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext S jE jF
    apply LinearMap.ext
    intro f
    simp only [LinearMap.comp_apply]
    rw [IsLocalizedModule.map_apply]
    exact map_localization_compatibility S j a f
  apply (IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective jE jF).mp
  rw [hmap]
  intro g
  change ∃ f : Module.End Rₛ Mₛ, QuotSMulTop.map a' f = g
  let e : Module.End Rₛ (QuotSMulTop a' Mₛ) ≃ₗ[Rₛ]
      Module.End (Rₛ ⧸ Ideal.span {a'}) (QuotSMulTop a' Mₛ) :=
    LinearMap.extendScalarsOfSurjectiveEquiv Ideal.Quotient.mk_surjective
  obtain ⟨z, hz⟩ := quotientEndomorphism_surjective a' Mₛ (e g)
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨f, e.injective hz⟩

end QuotSMulTop
