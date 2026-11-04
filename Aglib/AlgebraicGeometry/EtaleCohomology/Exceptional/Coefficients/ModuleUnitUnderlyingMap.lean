/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ModuleUnitInverseImage

/-! The original coefficient unit in the inverse scalar-forgetting coordinates. -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- The original inverse-image unit after the specified scalar-forgetting comparison. -/
theorem moduleUnitInverseImageIso_underlying_left {X S : Scheme.{u}} (f : S ⟶ X) (n : ℕ) :
    let Λ := ULift.{u + 1} (ZMod n)
    (moduleInverseImageUnderlyingIso Λ f).inv.app (moduleUnit X Λ) ≫
      (SheafOfModules.toSheaf (constantRing S Λ)).map (moduleUnitInverseImageIso f n).hom =
    (inverseImage f).map (moduleUnitUnderlyingIso X Λ).inv ≫
      (inverseImageConstantIso f).hom.app (AddCommGrpCat.of Λ) ≫
        (moduleUnitUnderlyingIso S Λ).hom := by
  dsimp only
  rw [moduleUnitInverseImageIso_underlying]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

end AlgebraicGeometry.Scheme.EtaleCohomology
