/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionLeftUnitIdentity
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionLeftUnitExpansion
public import Aglib.CategoryTheory.Functor.IdentitySourceExpansion

/-! # Actual source identity contraction of the left-unit supplied tower -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wD
variable {X Y : Scheme.{u}} {f : X ⟶ Y} (C : Hom.DenseCompactification f)
  (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hD : HasDerivedCategory.{wD} (ModuleSheaf C.Xbar Λ))

/-- The actual contraction and actual open expansion leave the original direct-image identity. -/
theorem moduleLeftUnitSourceExpansion_normalize :
    Functor.isoWhiskerRight (moduleDerivedIdentityFactorizationIso Λ X hX hX)
        (@moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hD) ≪≫
      Functor.leftUnitor (@moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hD) ≪≫
      moduleLeftUnitTargetExpansion C Λ hX hD =
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (@moduleDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX)
          (@moduleDerivedDirectImageIdIso Λ _ X hX) ≪≫
        Functor.rightUnitor (@moduleDerivedLowerShriek X X (𝟙 X) _ Λ _ hX hX))
      (@moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX hD) :=
  identitySourceExpansion (@moduleDerivedLowerShriekIdIso Λ _ X hX)
    (@moduleDerivedDirectImageIdIso Λ _ X hX)
    (moduleDerivedIdentityFactorizationIso Λ X hX hX)
    (moduleLeftUnitTargetExpansion C Λ hX hD)
    (@moduleDerivedIdentityFactorizationIso_sameModel X Λ _ hX)
    (moduleLeftUnitTargetExpansion_identity C Λ hX hD)

end AlgebraicGeometry.Scheme.EtaleCohomology
