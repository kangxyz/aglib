/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Localization.Module

/-! The original evaluation map after localization, without assuming global reflexivity. -/

@[expose] public section

noncomputable section

namespace Module.Dual

variable {R M Mₛ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Mₛ] [Module R Mₛ]
variable (S : Submonoid R) (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ]
  [IsLocalization S Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
variable (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f]
variable [Module.FinitePresentation R M] [Module.FinitePresentation R (Dual R M)]

/-- Finite-presentation dual base change identifies the original localized evaluation with
ordinary evaluation over the localized ring. -/
theorem localized_eval_eq :
    IsLocalizedModule.map S f
      (IsLocalizedModule.mapExtendScalars S
        (IsLocalizedModule.mapExtendScalars S f (Algebra.linearMap R Rₛ) Rₛ)
        (Algebra.linearMap R Rₛ) Rₛ) (eval R M) = (eval Rₛ Mₛ).restrictScalars R := by
  let d : Dual R M →ₗ[R] Dual Rₛ Mₛ :=
    IsLocalizedModule.mapExtendScalars S f (Algebra.linearMap R Rₛ) Rₛ
  let dd : Dual R (Dual R M) →ₗ[R] Dual Rₛ (Dual Rₛ Mₛ) :=
    IsLocalizedModule.mapExtendScalars S d (Algebra.linearMap R Rₛ) Rₛ
  apply IsLocalizedModule.linearMap_ext S f dd
  apply LinearMap.ext
  intro m
  change IsLocalizedModule.map S f dd (eval R M) (f m) = eval Rₛ Mₛ (f m)
  rw [IsLocalizedModule.map_apply]
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.linearMap_ext S d (Algebra.linearMap R Rₛ)
  apply LinearMap.ext
  intro l
  change IsLocalizedModule.map S d (Algebra.linearMap R Rₛ)
    (eval R M m) (d l) = d l (f m)
  rw [IsLocalizedModule.map_apply]
  exact (IsLocalizedModule.map_apply S f (Algebra.linearMap R Rₛ) l m).symm

include Rₛ f in
/-- Local reflexivity makes the actual canonical localization of the original evaluation
bijective. No global reflexivity assumption is used. -/
theorem localized_eval_bijective [Module.IsReflexive Rₛ Mₛ] :
    Function.Bijective (LocalizedModule.map S (eval R M)) := by
  let d := IsLocalizedModule.mapExtendScalars S f (Algebra.linearMap R Rₛ) Rₛ
  let dd := IsLocalizedModule.mapExtendScalars S d (Algebra.linearMap R Rₛ) Rₛ
  apply (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective f dd).mp
  rw [show IsLocalizedModule.map S f dd (eval R M) =
      (eval Rₛ Mₛ).restrictScalars R from localized_eval_eq S Rₛ f]
  exact Module.bijective_dual_eval Rₛ Mₛ

end Module.Dual
