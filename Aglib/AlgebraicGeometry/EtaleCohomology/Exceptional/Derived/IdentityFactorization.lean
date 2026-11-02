/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.LowerShriekComposition
public import Aglib.Algebra.Homology.DerivedCategory.Plus.ExactDerivedContractionModels
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ChangeTargetUnit

/-! # Original identity factorization through an independent middle derived model -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor DerivedCategory.Plus

namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u dE dM
variable (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u})

/-- The original ordinary lower-shriek/direct-image identity contraction. -/
def moduleIdentityFactorizationIso :
    moduleLowerShriek (𝟙 X) Λ ⋙ moduleDirectImage (𝟙 X) Λ ≅ 𝟭 (ModuleSheaf X Λ) :=
  isoWhiskerRight (moduleLowerShriekIdIso Λ X) _ ≪≫
    leftUnitor _ ≪≫ moduleDirectImageIdIso Λ X

instance moduleDirectImageId_preservesHomology :
    (moduleDirectImage (𝟙 X) Λ).PreservesHomology := by
  let : PreservesFiniteColimits (moduleDirectImage (𝟙 X) Λ) :=
    preservesFiniteColimits_of_natIso (moduleDirectImageIdIso Λ X).symm
  infer_instance

variable (hE : HasDerivedCategory.{dE} (ModuleSheaf X Λ))
  (hM : HasDerivedCategory.{dM} (ModuleSheaf X Λ))

/-- The original derived identity factorization, without identifying the middle model. -/
def moduleDerivedIdentityFactorizationIso :
    (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hE hM (moduleLowerShriek (𝟙 X) Λ) _ _) ⋙
      (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hM hE (moduleDirectImage (𝟙 X) Λ) _ _) ≅ 𝟭
        ((@DerivedCategory.Plus _ _ _ hE)) :=
  @exactDerivedContractionViaIso (ModuleSheaf X Λ) _ _ _ hE
    (ModuleSheaf X Λ) _ _ _ hM (moduleLowerShriek (𝟙 X) Λ)
    (moduleDirectImage (𝟙 X) Λ) _ _ _ (moduleIdentityFactorizationIso Λ X)

end AlgebraicGeometry.Scheme.EtaleCohomology
