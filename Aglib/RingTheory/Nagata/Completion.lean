/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.ReducedCompletion

/-!
# Dimension-bounded compatibility for reduced completion

The original one- and two-dimensional APIs use the single arbitrary-dimensional construction.
Their original rings, hypotheses, completion and numerical bounds are preserved.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

/-- The original one-dimensional reduced-completion interface. -/
theorem IsNagataRing.isReduced_completion_of_dimLE_one
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    (h : IsNagataRing.{u, 0} R) (hdim : ringKrullDim R ≤ 1) :
    IsReduced (AdicCompletion (maximalIdeal R) R) :=
  h.isReduced_completion_of_dimLE 1 hdim

/-- The original two-dimensional reduced-completion interface. -/
theorem IsNagataRing.isReduced_completion_of_dimLE_two
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    (h : IsNagataRing.{u, 0} R) (hdim : ringKrullDim R ≤ 2) :
    IsReduced (AdicCompletion (maximalIdeal R) R) :=
  h.isReduced_completion_of_dimLE 2 hdim
