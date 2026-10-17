/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Flat
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward.Shift
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition.Shift
public import Aglib.Algebra.Homology.CochainComplexPlus.QuasiIsoShift
public import Aglib.CategoryTheory.Functor.Derived.RightDerivedCommShift

/-!
# Native shifts of the original derived flat base-change map

The original base-change descent commutes with integer shifts: its defining
ordinary-mate transformation and both installed composite units commute
with shifts, and native right-derived uniqueness preserves this square.
This is the existing geometric map, not an independently chosen comparison.
No quasicoherence, Noetherianity or invertibility premise is needed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The standard derived-category structure on the indicated module category. -/
local instance baseChangeShiftStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The installed exact flat pullback uses the original right-derived shifts. -/
instance derivedFlatPullbackPlusCommShift {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    (derivedFlatPullbackPlus f).CommShift ℤ :=
  inferInstanceAs ((pullback f).rightDerivedFunctorPlus.CommShift ℤ)

/-- Deprecated compatibility name for `derivedFlatPullbackPlusCommShift`. -/
-- Preserve the public data name without registering a second shift instance.
@[deprecated (since := "2026-10-17"), nolint defsWithUnderscore]
alias derivedFlatPullbackPlus_commShift := derivedFlatPullbackPlusCommShift

/-- The installed flat pullback is triangulated for those same native shifts. -/
instance derivedFlatPullbackPlus_isTriangulated {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    (derivedFlatPullbackPlus f).IsTriangulated :=
  inferInstanceAs ((pullback f).rightDerivedFunctorPlus.IsTriangulated)

variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
    (h : IsPullback a b f j) [Flat j]

/-- The existing derived flat base-change map commutes with shifts, with
flatness of its other leg obtained from the original Cartesian square. -/
instance derivedFlatBaseChangeMap_commShift :
    letI := flat_cartesian_baseChange a b f j h
    (derivedFlatBaseChangeMap a b f j h).CommShift ℤ := by
  let := flat_cartesian_baseChange a b f j h
  let F := pushforward f
  let J := pullback j
  let A := pullback a
  let B := pushforward b
  let := F.isRightDerivedFunctor_comp_of_preservesHomology J
  let β := Functor.whiskerRight
    (NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h))
      DerivedCategory.Plus.Q ≫ Functor.rightDerivedFunctorPlusCompUnit A B
  apply Functor.commShift_of_rightDerived_fac
    (RF := F.rightDerivedFunctorPlus ⋙ J.rightDerivedFunctorPlus)
    (G := A.rightDerivedFunctorPlus ⋙ B.rightDerivedFunctorPlus)
    (Functor.rightDerivedFunctorPlusCompUnit F J) (CochainComplex.Plus.quasiIso U.Modules) ℤ
    (derivedFlatBaseChangeMap a b f j h) β
  ext K : 2
  exact derivedFlatBaseChangeMap_unit a b f j h K

end AlgebraicGeometry.Scheme.Modules
