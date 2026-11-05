/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.CategoryTheory.Abelian.ObjectProperty.Annihilator
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ObjectProperty
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Noetherian.Basic

/-! # Finite-type module annihilator induction for original derived functors

Finite generation is always over the original Noetherian coefficient ring.
No finiteness of the underlying group is required. An exact coefficient
functor retains the native kernel inclusion and cokernel projection.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

universe r m u v u' v' w w'

variable (R : Type r) [Ring R] [IsNoetherianRing R]

/-- Finite-type coefficients reduce to the prime divisors of their positive
annihilator using their original scalar kernels and quotient projections. -/
theorem property_of_positive_annihilator (P : ObjectProperty (ModuleCat.{m} R))
    (hzero : ∀ M, IsZero M → P M)
    (hstep : ∀ S : ShortComplex (ModuleCat.{m} R), S.ShortExact →
      P S.X₁ → P S.X₃ → P S.X₂)
    (n : ℕ) (hn : 0 < n)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ n →
      ∀ M : ModuleCat.{m} R, ∀ [Module.Finite R M], (∀ x : M, p • x = 0) → P M)
    (M : ModuleCat.{m} R) [Module.Finite R M] (hM : ∀ x : M, n • x = 0) : P M := by
  apply ObjectProperty.property_of_positive_annihilator
    (fun N : ModuleCat.{m} R => Module.Finite R N) P
    ?_ ?_ hzero hstep n hn ?_ M inferInstance ?_
  · intro A B a hA hB
    let := hA
    exact Module.Finite.of_injective (kernel.ι a).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  · intro A B a hA hB
    let := hB
    exact Module.Finite.of_surjective (cokernel.π a).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  · intro p hp hpn N hN hk
    let := hN
    apply hprime p hp hpn N
    intro x
    simpa using congrArg (fun a : N ⟶ N => a x) hk
  · ext x
    simpa using hM x

/-- A weak-Serre target property of the original derived images propagates
from prime-killed finite-type coefficients along an exact original coefficient
functor. The source and target derived-category universes are independent. -/
theorem rightDerived_property_of_positive_annihilator
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    [HasDerivedCategory.{w} A]
    {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
    (K : ModuleCat.{m} R ⥤ A) [K.Additive]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (F : A ⥤ B) [F.Additive]
    (P : ObjectProperty B) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]
    (n : ℕ) (hn : 0 < n)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ n →
      ∀ M : ModuleCat.{m} R, ∀ [Module.Finite R M], (∀ x : M, p • x = 0) →
        ∀ q : ℕ, P ((F.rightDerived q).obj (K.obj M)))
    (M : ModuleCat.{m} R) [Module.Finite R M] (hM : ∀ x : M, n • x = 0)
    (q : ℕ) : P ((F.rightDerived q).obj (K.obj M)) := by
  apply property_of_positive_annihilator R
    (fun N => ∀ j : ℕ, P ((F.rightDerived j).obj (K.obj N)))
    ?_ ?_ n hn hprime M hM q
  · intro N hN j
    exact P.prop_of_isZero ((F.rightDerived j).map_isZero (K.map_isZero hN))
  · intro S hS h₁ h₃ j
    exact F.rightDerived_property_of_shortExact P (S.map K) (hS.map_of_exact K) h₁ h₃ j

end ModuleCat
