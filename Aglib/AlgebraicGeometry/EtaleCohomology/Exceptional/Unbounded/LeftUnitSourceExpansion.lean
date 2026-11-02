/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.UnitIdentityValue
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionLeftUnitExpansion
public import Aglib.CategoryTheory.Functor.IdentitySourceExpansion

/-! # Actual source identity contraction of the left-unit supplied tower -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

universe u wX wD
variable {X Y : Scheme.{u}} {f : X ⟶ Y} (C : Hom.DenseCompactification f)
  (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hD : HasDerivedCategory.{wD} (ModuleSheaf C.Xbar Λ))

/-- The category structure for the specified derived-category model. -/
local instance sourceExpansionEndpointCategory : Category.{wX}
    (@DerivedCategory (ModuleSheaf X Λ) inferInstance inferInstance hX) :=
  @instCategoryDerivedCategory (ModuleSheaf X Λ) inferInstance inferInstance hX
/-- The category structure for the specified derived-category model. -/
local instance sourceExpansionAmbientCategory : Category.{wD}
    (@DerivedCategory (ModuleSheaf C.Xbar Λ) inferInstance inferInstance hD) :=
  @instCategoryDerivedCategory (ModuleSheaf C.Xbar Λ) inferInstance inferInstance hD

/-- The actual contraction and actual open expansion leave the original direct-image identity. -/
theorem moduleUnboundedLeftUnitSourceExpansion_normalize :
    Functor.isoWhiskerRight (moduleUnboundedSingleIdentityValueIso (hX := hX) (hM := hX) X Λ)
        (@moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hD) ≪≫
      Functor.leftUnitor (@moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hD) ≪≫
      moduleUnboundedLeftUnitTargetExpansion C Λ hX hD =
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (@moduleUnboundedDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX)
          (@moduleUnboundedDerivedDirectImageIdIso Λ _ X hX) ≪≫
        Functor.rightUnitor (@moduleUnboundedDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX))
      (@moduleUnboundedDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hD) :=
  identitySourceExpansion (@moduleUnboundedDerivedLowerShriekIdIso Λ _ X hX)
    (@moduleUnboundedDerivedDirectImageIdIso Λ _ X hX)
    (moduleUnboundedSingleIdentityValueIso (hX := hX) (hM := hX) X Λ)
    (moduleUnboundedLeftUnitTargetExpansion C Λ hX hD)
    (@moduleUnboundedSingleIdentityValueIso_sameModel X Λ _ hX)
    (moduleUnboundedLeftUnitTargetExpansion_identity C Λ hX hD)

end AlgebraicGeometry.Scheme.EtaleCohomology
