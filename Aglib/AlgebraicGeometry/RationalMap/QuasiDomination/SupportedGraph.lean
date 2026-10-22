/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.Basic

/-!
# Global closedness of a supported local graph

A local closed graph inside an open ambient subscheme need not be globally
closed. It is globally closed if its original schematically dense map lands
in an actual globally closed subscheme that itself factors through that open.
The closed-target lift retains the original map, including nilpotent data.
Density is required only in the local graph domain, never in the ambient base.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

variable {T D A₀ A G : Scheme.{u}}
    (o : A₀ ⟶ A) [IsOpenImmersion o]
    (c : G ⟶ A) [IsClosedImmersion c]
    (r : G ⟶ A₀) (hr : r ≫ o = c)
    (h : D ⟶ A₀) (j : T ⟶ D) [IsSchemeTheoreticallyDominant j]
    (g : T ⟶ G) (w : j ≫ (h ≫ o) = g ≫ c)

include hr in
/-- The native closed-target lift also preserves the literal local graph.
Its original-source triangle is `comp_closedTargetLift`. -/
theorem closedTargetLift_comp_of_open_factor :
    closedTargetLift j c (h ≫ o) g w ≫ r = h := by
  apply (cancel_mono o).mp
  rw [Category.assoc, hr, closedTargetLift_comp]

include hr in
/-- The actual factor of a supported local closed graph is a closed immersion. -/
theorem isClosedImmersion_closedTargetLift_of_open_factor [IsClosedImmersion h] :
    IsClosedImmersion (closedTargetLift j c (h ≫ o) g w) := by
  have : IsClosedImmersion (r ≫ o) := by rw [hr]; infer_instance
  have : IsClosedImmersion r := IsClosedImmersion.of_comp r o
  have : IsClosedImmersion (closedTargetLift j c (h ≫ o) g w ≫ r) := by
    rw [closedTargetLift_comp_of_open_factor o c r hr h j g w]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ r

include hr j g w in
/-- A locally closed graph supported in a global closed target is globally
closed. Only the original source's density in the local graph domain is used. -/
theorem isClosedImmersion_comp_of_supported_dense_factor [IsClosedImmersion h] :
    IsClosedImmersion (h ≫ o) := by
  have := isClosedImmersion_closedTargetLift_of_open_factor o c r hr h j g w
  rw [← closedTargetLift_comp j c (h ≫ o) g w]
  infer_instance

end AlgebraicGeometry.Scheme.QuasiDomination
