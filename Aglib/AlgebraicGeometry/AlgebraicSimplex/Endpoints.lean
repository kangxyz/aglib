/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AlgebraicSimplex.Basic

/-!
# The zero-face coordinate parameter
-/

@[expose] public section


namespace AlgebraicGeometry.AlgebraicSimplex
universe u
variable (K : Type u) [Field K]

theorem face_zero_parameter :
    AlgebraicSimplex.face K (0 : Fin 2) (AlgebraicSimplex.coordinate K 1 1) = 1 := by
  have h := AlgebraicSimplex.face_coordinate_succAbove K (0 : Fin 2) (0 : Fin 1)
  have hc : AlgebraicSimplex.coordinate K 0 0 = 1 := by
    simpa using AlgebraicSimplex.sum_coordinate K 0
  simpa using h.trans hc

end AlgebraicGeometry.AlgebraicSimplex

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/AlgebraicSimplex/Endpoints.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 0c57d2f0bb679564e3f116bf118195e08fe1c07458aaf4a7839802a4a840e682.
Native names and imports replace the source wrappers; stated conditions and maps are retained. -/
