/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Excellent.LocalFormalFiber

/-! # Excellent DVRs have geometrically reduced completed fraction fields

Only the standard G-ring component of excellence is consumed. The finite-type
algebra test universe `max u v` in the hypothesis remains explicit; the
auxiliary universe `v` is unrestricted.
-/

@[expose] public noncomputable section

universe u v

namespace IsExcellentRing

/-- Standard excellence of a DVR supplies the intrinsic completed-fraction-field
condition used by the downstream Artin approximation theorem. -/
theorem hasGeometricallyReducedFractionCompletion
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (h : IsExcellentRing.{u, v} R) :
    AdicCompletion.HasGeometricallyReducedFractionCompletion R :=
  IsGRing.hasGeometricallyReducedFractionCompletion R h.isGRing

end IsExcellentRing
