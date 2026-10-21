/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Reflexive.Localization

/-! Localization preserves the native reflexivity predicate without assuming freeness. -/

@[expose] public section

noncomputable section

example {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.IsReflexive R M]
    (S : Submonoid R) :
    Module.IsReflexive (Localization S) (LocalizedModule S M) := by
  let := Module.finitePresentation_of_finite R M
  let := Module.finitePresentation_of_finite R (Module.Dual R M)
  exact Module.IsReflexive.of_isLocalizedModule S (Localization S)
    (LocalizedModule.mkLinearMap S M)

example {R M Mₛ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup Mₛ] [Module R Mₛ] (S : Submonoid R)
    (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
    [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    [Module.FinitePresentation R M] [Module.FinitePresentation R (Module.Dual R M)]
    [Module.IsReflexive R M] (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f] :
    Function.Bijective (Module.Dual.eval Rₛ Mₛ) := by
  let := Module.IsReflexive.of_isLocalizedModule S Rₛ f
  exact Module.bijective_dual_eval Rₛ Mₛ
