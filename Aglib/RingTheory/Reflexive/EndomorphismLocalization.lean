/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.Module

/-! An actual endomorphism action localizes to conjugation along a localized isomorphism. -/

@[expose] public section

noncomputable section

namespace LinearMap

variable {R Rₛ M N Mₛ Nₛ : Type*} [CommRing R] [CommRing Rₛ] [Algebra R Rₛ]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
  [AddCommGroup Nₛ] [Module R Nₛ] [Module Rₛ Nₛ] [IsScalarTower R Rₛ Nₛ]
  [Module.FinitePresentation R M] [Module.FinitePresentation R N]

/-- An endomorphism action intertwined by a map which becomes an isomorphism is itself
bijective after localization. This concerns the actual localized action, not an abstract
isomorphism of its source and target. -/
theorem localized_endomorphismMap_bijective
    (S : Submonoid R) [IsLocalization S Rₛ]
    (jM : M →ₗ[R] Mₛ) (jN : N →ₗ[R] Nₛ)
    [IsLocalizedModule S jM] [IsLocalizedModule S jN]
    (a : M →ₗ[R] N) (g : Module.End R M →ₗ[R] Module.End R N)
    (hnat : ∀ f, (g f).comp a = a.comp f)
    (ha : Function.Bijective (IsLocalizedModule.mapExtendScalars S jM jN Rₛ a)) :
    Function.Bijective (LocalizedModule.map S g) := by
  let e := LinearEquiv.ofBijective (IsLocalizedModule.mapExtendScalars S jM jN Rₛ a) ha
  let jE := IsLocalizedModule.mapExtendScalars S jM jM Rₛ
  let jF := IsLocalizedModule.mapExtendScalars S jN jN Rₛ
  have hcomm (f : Module.End R M) :
      (jF (g f)).comp e.toLinearMap = e.toLinearMap.comp (jE f) := by
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.linearMap_ext S jM jN
    apply LinearMap.ext
    intro x
    change IsLocalizedModule.map S jN jN (g f)
        (IsLocalizedModule.map S jM jN a (jM x)) =
      IsLocalizedModule.map S jM jN a (IsLocalizedModule.map S jM jM f (jM x))
    simp only [IsLocalizedModule.map_apply]
    exact congrArg jN (DFunLike.congr_fun (hnat f) x)
  have hg : IsLocalizedModule.map S jE jF g = e.conj.toLinearMap.restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext S jE jF
    apply LinearMap.ext
    intro f
    simp only [LinearMap.comp_apply]
    rw [IsLocalizedModule.map_apply]
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
      LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, LinearMap.comp_apply]
      using DFunLike.congr_fun (hcomm f) x
  apply (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective jE jF).mp
  rw [hg]
  exact e.conj.bijective

end LinearMap
