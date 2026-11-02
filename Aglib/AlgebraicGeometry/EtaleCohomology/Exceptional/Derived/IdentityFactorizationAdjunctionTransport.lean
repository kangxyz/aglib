/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.IdentityFactorizationCounit
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.TransportLeft

/-! # The identity contraction retains the installed inverse-image adjunction unit -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor DerivedCategory.Plus
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u dE dM
variable (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u})
  (hE : HasDerivedCategory.{dE} (ModuleSheaf X Λ))
  (hM : HasDerivedCategory.{dM} (ModuleSheaf X Λ))

/-- Derive the original ordinary identity comparison from inverse image to lower shriek. -/
def moduleDerivedIdentityInverseToShriekIso :
    (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hE hM (moduleInverseImage (𝟙 X) Λ) _ _) ≅
      (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hE hM (moduleLowerShriek (𝟙 X) Λ) _ _) :=
  @Functor.rightDerivedFunctorPlusIso (ModuleSheaf X Λ) _ _ hE _
    (ModuleSheaf X Λ) _ _ hM (moduleInverseImage (𝟙 X) Λ) _
    (moduleLowerShriek (𝟙 X) Λ) _
    (moduleInverseImageIdIso Λ X ≪≫ (moduleLowerShriekIdIso Λ X).symm)

/-- The contraction is normalized by the original installed inverse-image/direct-image unit. -/
theorem moduleDerivedIdentityFactorizationIso_installed_unit :
    (@moduleDerivedAdjunction X Λ _ X (𝟙 X) hE hM).unit ≫
      whiskerRight (moduleDerivedIdentityInverseToShriekIso Λ X hE hM).hom
        ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hM hE (moduleDirectImage (𝟙 X) Λ) _ _)) =
      (moduleDerivedIdentityFactorizationIso Λ X hE hM).inv := by
  have h := @Adjunction.rightDerivedFunctorPlus_ofNatIsoLeft_unit
    (ModuleSheaf X Λ) _ _ hE _ (ModuleSheaf X Λ) _ _ hM _
    (moduleInverseImage (𝟙 X) Λ) (moduleLowerShriek (𝟙 X) Λ)
    (moduleDirectImage (𝟙 X) Λ) _ _ _ _ _
    (moduleInverseImageAdjunction (𝟙 X) Λ)
    (moduleInverseImageIdIso Λ X ≪≫ (moduleLowerShriekIdIso Λ X).symm)
  exact h.symm.trans (moduleDerivedIdentityFactorizationAdjunction_unit_eq_inv Λ X hE hM)

end AlgebraicGeometry.Scheme.EtaleCohomology
