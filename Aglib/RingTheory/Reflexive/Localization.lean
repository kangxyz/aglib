/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Localization of reflexive modules

Finite presentation of a module and its dual makes the canonical double-dual evaluation
compatible with localization. Consequently localization preserves native module reflexivity.
The Noetherian finite-module case supplies the localization step in the Auslander purity
argument; no normality or purity theorem is assumed here.
-/

@[expose] public section

noncomputable section

namespace Module

variable {R M Mₛ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Mₛ] [Module R Mₛ]
variable (S : Submonoid R) (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ]
  [IsLocalization S Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
variable (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f]
variable [FinitePresentation R M] [FinitePresentation R (Dual R M)]

include S f in
/-- Reflexivity is preserved by localization when the module and its dual are finitely
presented. The conclusion concerns the ordinary evaluation map over the localized ring. -/
theorem IsReflexive.of_isLocalizedModule [IsReflexive R M] : IsReflexive Rₛ Mₛ := by
  let d : Dual R M →ₗ[R] Dual Rₛ Mₛ :=
    IsLocalizedModule.mapExtendScalars S f (Algebra.linearMap R Rₛ) Rₛ
  let dd : Dual R (Dual R M) →ₗ[R] Dual Rₛ (Dual Rₛ Mₛ) :=
    IsLocalizedModule.mapExtendScalars S d (Algebra.linearMap R Rₛ) Rₛ
  let e : Mₛ ≃ₗ[Rₛ] Dual Rₛ (Dual Rₛ Mₛ) :=
    IsLocalizedModule.mapEquiv S f dd Rₛ (evalEquiv R M)
  have h_eval (m : M) : dd (Dual.eval R M m) = Dual.eval Rₛ Mₛ (f m) := by
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.linearMap_ext S d (Algebra.linearMap R Rₛ)
    apply LinearMap.ext
    intro l
    change IsLocalizedModule.map S d (Algebra.linearMap R Rₛ)
        (Dual.eval R M m) (d l) = d l (f m)
    rw [IsLocalizedModule.map_apply]
    exact (IsLocalizedModule.map_apply S f (Algebra.linearMap R Rₛ) l m).symm
  have he : e.toLinearMap = Dual.eval Rₛ Mₛ := by
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.linearMap_ext S f dd
    apply LinearMap.ext
    intro m
    change IsLocalizedModule.map S f dd (evalEquiv R M).toLinearMap (f m) = _
    rw [IsLocalizedModule.map_apply]
    exact h_eval m
  exact ⟨he ▸ e.bijective⟩

end Module
