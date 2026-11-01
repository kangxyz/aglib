/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.IdentityFactorization
public import Aglib.Algebra.Homology.DerivedCategory.Plus.ExactDerivedContractionIdentity

/-! # Original identity contraction at the endpoint model

This internal normalization does not restrict any final compactification family.
The separate original mixed-family comparison transports the identity-middle model.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX
variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- The original contraction agrees with the two original native identity comparisons. -/
theorem moduleDerivedIdentityFactorizationIso_sameModel :
    moduleDerivedIdentityFactorizationIso Λ X hX hX =
      Functor.isoWhiskerRight (moduleDerivedLowerShriekIdIso Λ X)
        (moduleDerivedDirectImage Λ (𝟙 X)) ≪≫
      Functor.leftUnitor (moduleDerivedDirectImage Λ (𝟙 X)) ≪≫
        moduleDerivedDirectImageIdIso Λ X := by
  have he : moduleIdentityFactorizationIso Λ X =
      (Functor.isoWhiskerRight (moduleLowerShriekIdIso Λ X)
        (moduleDirectImage (𝟙 X) Λ) ≪≫
        Functor.leftUnitor (moduleDirectImage (𝟙 X) Λ)) ≪≫ moduleDirectImageIdIso Λ X :=
    (Iso.trans_assoc _ _ _).symm
  unfold moduleDerivedIdentityFactorizationIso
  rw [he]
  exact DerivedCategory.Plus.exactDerivedContractionViaIso_identity
    (moduleLowerShriek (𝟙 X) Λ) (moduleDirectImage (𝟙 X) Λ)
    (moduleLowerShriekIdIso Λ X) (moduleDirectImageIdIso Λ X)

end AlgebraicGeometry.Scheme.EtaleCohomology
