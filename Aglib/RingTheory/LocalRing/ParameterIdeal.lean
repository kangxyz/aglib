/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.LocalRing.ParameterFamily

/-! # Two-dimensional parameter-pair compatibility -/

@[expose] public noncomputable section

namespace IsLocalRing

/-- A prescribed nonzero nonunit in a local Noetherian domain of
dimension at most two extends to an actual maximal-primary parameter
ideal with one additional element. -/
theorem exists_parameter_pair_containing
    (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 2 R] (a : R) (ha0 : a ≠ 0) (ha : a ∈ maximalIdeal R) :
    ∃ x : R, x ∈ maximalIdeal R ∧
      (Ideal.span {a} ⊔ Ideal.span {x}).radical = maximalIdeal R := by
  obtain ⟨x, hx, hrad⟩ := exists_parameter_family_containing R 1
    (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 2 R)) a ha0 ha
  refine ⟨x 0, hx 0, ?_⟩
  simpa only [Set.range_unique, show (default : Fin 1) = 0 from Subsingleton.elim _ _]
    using hrad

end IsLocalRing
