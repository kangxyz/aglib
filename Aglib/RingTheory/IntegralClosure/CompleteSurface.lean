/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.NormalExtension
public import Aglib.RingTheory.IntegralClosure.PurelyInseparable.CompleteLocalSurface

/-!
# Finite normalization of a complete normal local surface

The literal normalization of a complete Noetherian normal local domain of
dimension at most two is finite in every finite fraction-field extension.
The purely inseparable case is supplied by the actual height-one residue
layers and coefficient lifting. A finite normal hull then reduces the general
extension to a purely inseparable fixed field followed by a separable extension.
The original field embedding and coefficient action are retained throughout.

This does not cover a nonnormal complete base or establish a resolution.
-/

@[expose] public noncomputable section

namespace integralClosure

variable (R K L : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [IsLocalRing R] [Ring.KrullDimLE 2 R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [FiniteDimensional K L]

include K

/-- Normalization in every finite fraction-field extension is finite over the
original complete normal Noetherian local base of dimension at most two. -/
theorem finite_of_complete_local_normal_dimLE_two :
    Module.Finite R (integralClosure R L) := by
  apply finite_of_finite_pure_extensions R K L
  intro E _ _ _ _ _ _
  exact finite_of_complete_local_normal_dimLE_two_of_isPurelyInseparable R K E

end integralClosure
