/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Computation.DimensionShift
public import Aglib.Algebra.Homology.CochainComplex.Cycles

/-! # Finite dimension shifting on the actual cycles of an unbounded complex

Only one uniform vanishing degree is required. The finite induction moves to
cycles further to the left; it imposes no bound on the complex itself.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe s u v w u' v' w'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [IsGrothendieckAbelian.{s} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive]
  (K : CochainComplex C ℤ) (hK : K.Acyclic)
  (hterms : ∀ i : ℤ, ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj (K.X i)))

include hK hterms in
/-- Finite dimension shifting on actual cycles, starting at any positive degree. -/
theorem isZero_rightDerived_cycles_of_bound (k n : ℕ)
    (hbound : ∀ M : C, IsZero ((F.rightDerived (n + k + 1)).obj M)) (i : ℤ) :
    IsZero ((F.rightDerived (n + 1)).obj (K.cycles i)) := by
  induction k generalizing n i with
  | zero => exact hbound _
  | succ k ih =>
    have hz : IsZero ((F.rightDerived (n + 1 + 1)).obj (K.cycles (i - 1))) :=
      ih (n + 1) (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hbound) (i - 1)
    have h := F.isZero_rightDerived_X₃_of_shortExact
      (K.cycleSequence_shortExact (i - 1) (hK _)) (n + 1) (hterms (i - 1) n) hz
    simpa only [CochainComplex.cycleSequence, sub_add_cancel] using h

variable [PreservesFiniteLimits F]

include hK hterms in
/-- A finite cohomological-dimension bound makes the original termwise image
of an acyclic complex of acyclic coefficients acyclic, without any truncation. -/
theorem acyclic_map_of_acyclic_terms_of_bound (N : ℕ)
    (hbound : ∀ M : C, IsZero ((F.rightDerived (N + 1)).obj M)) :
    ((F.mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  apply CochainComplex.acyclic_map_of_cycle_sequences F K
  intro i
  apply F.shortExact_map_of_isZero_rightDerived_one (K.cycleSequence_shortExact i (hK _))
  exact F.isZero_rightDerived_cycles_of_bound K hK hterms N 0
    (by simpa only [Nat.zero_add] using hbound) i

end CategoryTheory.Functor
