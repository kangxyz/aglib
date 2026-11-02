/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.PointSupportedSubobject

/-! # The actual universal property of the geometric-point supported subobject -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} {A F : AbelianSheaf.{u, u + 1} X}

/-- A morphism factors through the actual supported subobject precisely when its
composites with all outside-point units vanish. -/
theorem pointSupportedSubobject_factors_iff (Z : Set X) (a : A ⟶ F) :
    (pointSupportedSubobject F Z).Factors a ↔
      ∀ (x : X), x ∉ Z → a ≫
        (pointSmallEtale (FibrewiseClosed.geometricPoint x)).skyscraperSheafAdjunction.unit.app F =
          0 := by
  exact Adjunction.kernelSupport_factors_iff.{u + 1}
    (fun x : X => (pointSmallEtale (FibrewiseClosed.geometricPoint x)).skyscraperSheafAdjunction
      (A := Ab.{u + 1})) F Z a

/-- The original native factor through the supported subobject composes to the given morphism. -/
theorem pointSupportedSubobject_factorThru_arrow (Z : Set X) (a : A ⟶ F)
    (h : ∀ (x : X), x ∉ Z → a ≫
      (pointSmallEtale (FibrewiseClosed.geometricPoint x)).skyscraperSheafAdjunction.unit.app F =
        0) :
    (pointSupportedSubobject F Z).factorThru a
        ((pointSupportedSubobject_factors_iff Z a).mpr h) ≫
      (pointSupportedSubobject F Z).arrow = a := by
  exact Adjunction.kernelSupport_factorThru_arrow.{u + 1}
    (fun x : X => (pointSmallEtale (FibrewiseClosed.geometricPoint x)).skyscraperSheafAdjunction
      (A := Ab.{u + 1})) F Z a h

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
