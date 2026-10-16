/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.Trace
public import Aglib.Algebra.Homology.Simplex.Relative.Empty

/-!
# Native scalar comparisons under an equality of required supports

Transport of the original empty/full-support homology equivalences retains
the original cycles quotient and vertex/increasing-tuple evaluation. These
equations let actual monomial supports use the native simplex comparisons
without replacing the original weight homology objects.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

namespace AlgebraicTopology.RelativeSimplex

variable (R : Type u) [Ring R]

/-- The original empty-support H0 comparison transported along the displayed
support equality. -/
def homologyZeroLinearEquivOfEqEmpty {ι : Type v} (S : Set ι) (hS : S = ∅) (j : ι) :
    (complex R S).homology 0 ≃ₗ[R] R := by
  subst S
  exact emptySupportHomologyZeroLinearEquiv j

/-- Equality transport retains the original cycles quotient and vertex evaluation. -/
theorem homologyZeroLinearEquivOfEqEmpty_homologyπ {ι : Type v}
    (S : Set ι) (hS : S = ∅) (j : ι) (c : (complex R S).cycles 0) :
    homologyZeroLinearEquivOfEqEmpty R S hS j ((complex R S).homologyπ 0 c) =
      (complex R S).iCycles 0 c ⟨fun _ => j, by rw [hS]; exact Set.empty_subset _⟩ := by
  subst S
  exact emptySupportHomologyZeroLinearEquiv_homologyπ j c

/-- The original full-support top comparison transported along the displayed
support equality. -/
def topHomologyLinearEquivOfEqUniv (n : ℕ) (S : Set (Fin (n + 1))) (hS : S = Set.univ) :
    (complex R S).homology n ≃ₗ[R] R := by
  subst S
  exact fullSupportTopLinearEquiv R n

/-- Equality transport retains the original cycles quotient and evaluation on
the increasing identity tuple, with its original positive sign. -/
theorem topHomologyLinearEquivOfEqUniv_homologyπ (n : ℕ)
    (S : Set (Fin (n + 1))) (hS : S = Set.univ) (c : (complex R S).cycles n) :
    topHomologyLinearEquivOfEqUniv R n S hS ((complex R S).homologyπ n c) =
      (complex R S).iCycles n c ⟨id, fun i _ => ⟨i, rfl⟩⟩ := by
  subst S
  exact fullSupportTopLinearEquiv_homologyπ n c

end AlgebraicTopology.RelativeSimplex
