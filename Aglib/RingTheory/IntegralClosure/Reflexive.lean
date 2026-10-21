/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Reflexive.Algebra
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Reflexivity of finite integral closures

The actual double dual embeds in the generic field, is finite over the base, contains one,
and is closed under multiplication. The determinant trick makes every element integral;
the defining property of the integral closure then recovers the original module. Generic
reflexivity is supplied only by finite-dimensional linear algebra over the fraction field.
-/

@[expose] public section

noncomputable section

namespace IsIntegralClosure

variable (R K L B : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [CommRing B] [Algebra R B] [Algebra B L] [IsScalarTower R B L]
  [IsIntegralClosure B R L] [Module.Finite R B] [FiniteDimensional K L]

include K L in
/-- A finite integral closure in a finite extension of the fraction field is reflexive over
a Noetherian domain. This proves native bijectivity of the original double-dual evaluation. -/
theorem isReflexive : Module.IsReflexive R B := by
  let : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) L :=
    IsIntegralClosure.isLocalization R K L B
  let j : B →ₐ[R] L := IsScalarTower.toAlgHom R B L
  let : IsLocalizedModule (nonZeroDivisors R) j.toLinearMap := inferInstance
  let := Module.finitePresentation_of_finite R B
  let := Module.finitePresentation_of_finite R (Module.Dual R B)
  let c := Module.Dual.doubleDualToFraction (K := K) j.toLinearMap
  have hc : Function.Injective c := Module.Dual.doubleDualToFraction_injective j.toLinearMap
  have hc_eval (b : B) : c (Module.Dual.eval R B b) = algebraMap B L b :=
    Module.Dual.doubleDualToFraction_eval j.toLinearMap b
  have h1 : (1 : L) ∈ c.range := by
    refine ⟨Module.Dual.eval R B 1, ?_⟩
    rw [hc_eval, map_one]
  have hne : c.range ≠ ⊥ := by
    intro he
    have : (1 : L) = 0 := by simpa only [he, Submodule.mem_bot] using h1
    exact one_ne_zero this
  have hint (g : Module.Dual R (Module.Dual R B)) : IsIntegral R (c g) := by
    apply isIntegral_of_smul_mem_submodule c.range hne (Submodule.fg_range c)
    intro y hy
    exact Module.Dual.mul_mem_range_doubleDualToFraction j ⟨g, rfl⟩ hy
  constructor
  constructor
  · intro b b' he
    apply IsIntegralClosure.algebraMap_injective B R L
    simpa only [hc_eval] using congrArg c he
  · intro g
    obtain ⟨b, hb⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp (hint g)
    refine ⟨b, hc ?_⟩
    rw [hc_eval]
    exact hb

end IsIntegralClosure
