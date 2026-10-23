/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.CohomologySquare

/-! # Original cohomology base-change square under exact direct image -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u wX wS wX' wS'
attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  [HasExt.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wS} (AbelianSheaf.{u, u + 1} S)]
  [HasExt.{wX'} (AbelianSheaf.{u, u + 1} X')]
  [HasExt.{wS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)


variable [PreservesFiniteColimits (directImage f)]
  [PreservesFiniteColimits (directImage f')]

/-- The original cohomology comparison commutes with original exchange and pullback.
Only exactness of the vertical direct images is used; the square need not be cartesian. -/
theorem cohomologyDirectImageAddEquiv_baseChange
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (a : Sheaf.H.{wS} ((directImage f).obj F) q) :
    cohomologyDirectImageAddEquiv f' ((inverseImage g').obj F) q
        (Sheaf.H.map ((baseChangeMap f f' g g' h).app F) q
          (cohomologyPullback g ((directImage f).obj F) q a)) =
      cohomologyPullback g' F q (cohomologyDirectImageAddEquiv f F q a) := by
  rw [cohomologyDirectImageAddEquiv_apply, cohomologyDirectImageAddEquiv_apply,
    cohomologyPullback_coefficientMap, ← Sheaf.H.map_comp_apply,
    baseChangeMap_counit, Sheaf.H.map_comp_apply]
  have hsq := cohomologyPullback_square f f' g g' h ((directImage f).obj F) q a
  have hn := cohomologyPullback_coefficientMap g'
    ((inverseImageAdjunction f).counit.app F) q
    (cohomologyPullback f ((directImage f).obj F) q a)
  exact (congrArg
    (Sheaf.H.map ((inverseImage g').map ((inverseImageAdjunction f).counit.app F)) q)
    hsq).trans hn.symm

end AlgebraicGeometry.Scheme.EtaleCohomology
