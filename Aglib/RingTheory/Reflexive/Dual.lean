/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Reflexive.DoubleDualFraction
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Localization.Finiteness

/-! Reflexivity of finite dual modules over a Noetherian domain. -/

@[expose] public section

noncomputable section

namespace Module

/-- A dual is reflexive when finite-presentation base change identifies its generic double
 dual with the original generic module. No reflexivity of the original module is assumed. -/
theorem IsReflexive.dual_of_generic
    {R K M Mₖ : Type*} [CommRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] [AddCommGroup Mₖ] [Module R Mₖ]
    [Module K Mₖ] [IsScalarTower R K Mₖ]
    [FinitePresentation R M] [IsReflexive K Mₖ]
    (f : M →ₗ[R] Mₖ) [IsLocalizedModule (nonZeroDivisors R) f] :
    IsReflexive R (Dual R M) := by
  let c := Dual.doubleDualToFraction (K := K) f
  constructor
  constructor
  · intro l t h
    apply LinearMap.ext
    intro m
    exact congrArg (fun g : Dual R (Dual R (Dual R M)) ↦ g (Dual.eval R M m)) h
  · intro t
    let l : Dual R M := t.comp (Dual.eval R M)
    refine ⟨l, ?_⟩
    apply LinearMap.ext
    intro g
    change g l = t g
    obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors R) f (c g)
    have hg : (s : R) • g = Dual.eval R M m := by
      apply Dual.doubleDualToFraction_injective (K := K) f
      simpa only [Submonoid.smul_def, map_smul, Dual.doubleDualToFraction_eval] using hs
    have hsreg : IsSMulRegular R (s : R) :=
      (isRegular_iff_mem_nonZeroDivisors.mpr s.property).isSMulRegular
    apply hsreg
    calc
      (s : R) • g l = ((s : R) • g) l := rfl
      _ = l m := by rw [hg]; rfl
      _ = t (Dual.eval R M m) := rfl
      _ = t ((s : R) • g) := by rw [hg]
      _ = (s : R) • t g := map_smul t _ _

/-- The dual of a finite module over a Noetherian domain is reflexive. -/
theorem IsReflexive.dual_of_finite {R M : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsReflexive R (Dual R M) := by
  let := finitePresentation_of_finite R M
  let f := LocalizedModule.mkLinearMap (nonZeroDivisors R) M
  let : Module.Finite (FractionRing R) (LocalizedModule (nonZeroDivisors R) M) :=
    Module.Finite.of_isLocalizedModule (nonZeroDivisors R) f
  exact IsReflexive.dual_of_generic (K := FractionRing R) f

end Module
