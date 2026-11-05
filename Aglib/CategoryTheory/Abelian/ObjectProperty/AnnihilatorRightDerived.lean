/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.CategoryTheory.Abelian.ObjectProperty.Annihilator
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ObjectProperty

/-! # Positive-annihilator induction through an exact coefficient functor

The source class only needs kernels and cokernels between its own objects.
The original exact coefficient functor carries their actual short exact
sequences to the input of the right-derived functor. No finite underlying
sets, arbitrary-subobject closure, or coefficient-ring characteristic enters.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ObjectProperty

universe uC vC uA vA uB vB wA wB

/-- A weak-Serre property of all original right-derived images reduces to
prime-killed objects in any kernel/cokernel-stable coefficient class. -/
theorem rightDerived_property_of_positive_annihilator
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
    [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (Q : ObjectProperty C)
    (hkernel : ∀ {M N : C} (a : M ⟶ N), Q M → Q N → Q (kernel a))
    (hcokernel : ∀ {M N : C} (a : M ⟶ N), Q M → Q N → Q (cokernel a))
    (K : C ⥤ A) [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (F : A ⥤ B) [F.Additive]
    (P : ObjectProperty B) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]
    (n : ℕ) (hn : 0 < n)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ n → ∀ M : C, Q M → p • 𝟙 M = 0 →
      ∀ q : ℕ, P ((F.rightDerived q).obj (K.obj M)))
    (M : C) (hM : Q M) (hkill : n • 𝟙 M = 0) (q : ℕ) :
    P ((F.rightDerived q).obj (K.obj M)) := by
  apply property_of_positive_annihilator Q
    (fun N => ∀ j : ℕ, P ((F.rightDerived j).obj (K.obj N)))
    hkernel hcokernel ?_ ?_ n hn hprime M hM hkill q
  · intro N hN j
    exact P.prop_of_isZero ((F.rightDerived j).map_isZero (K.map_isZero hN))
  · intro T hT h₁ h₃ j
    exact F.rightDerived_property_of_shortExact P (T.map K) (hT.map_of_exact K) h₁ h₃ j

end CategoryTheory.ObjectProperty
