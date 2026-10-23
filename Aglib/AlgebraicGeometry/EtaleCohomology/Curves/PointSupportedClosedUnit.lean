/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ClosedSupportUnit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.PointSupportedSubobject

/-! # Original closed-immersion units for the actual support subobjects -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

attribute [local instance] hasSheafifyLarge

/-- The actual support subobject is the direct image of its inverse image whenever
its chosen geometric points lift through the given closed immersion. -/
theorem pointSupportedSubobject_unit_isIso {S X : Scheme.{u}} (i : S ⟶ X)
    [IsClosedImmersion i] (F : AbelianSheaf.{u, u + 1} X) (Z : Set X)
    (hlift : ∀ x ∈ Z, ∃ z : Spec (.of (FibrewiseClosed.pointField x)) ⟶ S,
      z ≫ i = FibrewiseClosed.geometricPoint x) :
    IsIso ((inverseImageAdjunction i).unit.app
      (pointSupportedSubobject F Z : AbelianSheaf.{u, u + 1} X)) := by
  apply closedSupportUnit_isIso_of_pointFamily
  intro x hx
  apply pointSupportedSubobject_outside_stalk
  intro hZ
  obtain ⟨z, hz⟩ := hlift x hZ
  exact hx z hz

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
