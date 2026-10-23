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
  constructor
  · intro h x hx
    rw [← Subobject.factorThru_arrow _ _ h, Category.assoc,
      pointSupportedSubobject_arrow_unit F Z x hx, comp_zero]
  · intro h
    have hi : imageSubobject a ≤ pointSupportedSubobject F Z := by
      apply Subobject.le_sInf.{u + 1}
      rintro _ ⟨x, rfl⟩
      exact le_kernelSubobject _ _ (imageSubobject_arrow_comp_eq_zero (h x.val x.property))
    apply (Subobject.factors_iff _ _).mpr
    refine ⟨factorThruImageSubobject a ≫ Subobject.ofLE _ _ hi, ?_⟩
    change (factorThruImageSubobject a ≫ Subobject.ofLE _ _ hi) ≫
      (pointSupportedSubobject F Z).arrow = a
    rw [Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
