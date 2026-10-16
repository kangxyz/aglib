/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pushforward

/-!
# Native shift structures of installed derived direct image

The existing geometric derived pushforward and its existing unit carry
the native right-derived shift structures. These transparent instances
retain the original standard module-sheaf derived categories; no second
derived functor or shift structure is selected. Postnikov and geometric
base-change comparisons can consume the installed functor directly.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

local instance pushforwardShiftStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The original derived pushforward uses its native right-derived shifts. -/
instance derivedPushforwardPlus_commShift : (derivedPushforwardPlus f).CommShift ℤ :=
  inferInstanceAs ((pushforward f).rightDerivedFunctorPlus.CommShift ℤ)

/-- The installed derived pushforward is triangulated for those same shifts. -/
instance derivedPushforwardPlus_isTriangulated : (derivedPushforwardPlus f).IsTriangulated :=
  inferInstanceAs ((pushforward f).rightDerivedFunctorPlus.IsTriangulated)

/-- Its original unit commutes with the native shifts of both functors. -/
instance derivedPushforwardPlusUnit_commShift : (derivedPushforwardPlusUnit f).CommShift ℤ :=
  inferInstanceAs ((pushforward f).rightDerivedFunctorPlusUnit.CommShift ℤ)

end AlgebraicGeometry.Scheme.Modules
