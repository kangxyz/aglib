/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackComposition

/-! # Actual coefficient-image classes retain produced open zero

Generic effacement supplies zero of the original class along a composite
cover map. The original composition comparison and coefficient naturality
turn this into restriction zero of the actual transformed class. This step
does not assume that the transformed coefficient is the original coefficient.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u eY eZ eV
attribute [local instance] hasSheafifyLarge

/-- Composite zero of the original class becomes restriction zero of the
actual pulled-back and coefficient-mapped class. -/
theorem coefficient_restriction_zero_of_composite_zero
    {Y Z V : Scheme.{u}}
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eZ} (AbelianSheaf.{u, u + 1} Z)]
    [HasExt.{eV} (AbelianSheaf.{u, u + 1} V)]
    (v : Z ⟶ Y) (j : V ⟶ Z)
    (F : AbelianSheaf.{u, u + 1} Y) (G : AbelianSheaf.{u, u + 1} Z)
    (a : (inverseImage v).obj F ⟶ G) (q : ℕ) (c : Sheaf.H.{eY} F q)
    (hc : cohomologyPullback.{u, eY, eV} (j ≫ v) F q c = 0) :
    cohomologyPullback.{u, eZ, eV} j G q
      (Sheaf.H.map a q (cohomologyPullback.{u, eY, eZ} v F q c)) = 0 := by
  rw [cohomologyPullback_coefficientMap]
  have hcomp := cohomologyPullback_comp.{u, eY, eZ, eV} v j F q c
  rw [hc, map_zero] at hcomp
  rw [← hcomp, map_zero]

end AlgebraicGeometry.Scheme.EtaleCohomology
