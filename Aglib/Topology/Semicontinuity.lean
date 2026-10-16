/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Semicontinuity.Defs
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Locally constant sums of upper semicontinuous natural-valued functions

If two upper semicontinuous natural-valued functions have locally constant
sum, each is locally constant. The proof uses their original neighbourhood
dimension bounds. This supplies the numerical step in reduced-base
cohomology and base-change criteria.
-/

@[expose] public section

open scoped Topology

variable {X : Type*} [TopologicalSpace X] {f g : X → ℕ}

/-- An upper semicontinuous natural-valued summand is locally constant when the other
summand is upper semicontinuous and their sum is locally constant. -/
theorem UpperSemicontinuous.isLocallyConstant_of_add (hf : UpperSemicontinuous f)
    (hg : UpperSemicontinuous g) (h : IsLocallyConstant (fun x => f x + g x)) :
    IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_eventually_eq f).mpr
  intro x
  filter_upwards [h.eventually_eq x, hf x (f x + 1) (Nat.lt_succ_self _),
    hg x (g x + 1) (Nat.lt_succ_self _)] with y hsum hfy hgy
  omega
