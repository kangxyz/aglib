/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.BaseChangeIdentityAlgebra
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.BaseChangeCompositeUnit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenBaseChangeIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Refinement.ProperComparison

/-!
# The original identity-base compactified map is the refinement transition

The proper layer is the original identity-base unit contraction. The open
layer is the original Cartesian identity-source normalization. Their abstract
pasting identifies the actual map, not merely its invertibility class.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wC wD wS
variable {X C D S : Scheme.{u}} (jC : X ⟶ C) (jD : X ⟶ D)
  [IsOpenImmersion jC] [IsOpenImmersion jD]
  (h : C ⟶ D) (sq : IsPullback jC (𝟙 X) h jD) (pD : D ⟶ S)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

/-- The actual proper/open exchange over the identity base contracts to the
original proper-refinement unit and original structural compositor. -/
theorem moduleCompactifiedIdentityBaseEquation :
    CompactifiedIdentityBaseEquation
      (compositeExchange
        (moduleDerivedBaseChangeMap Λ pD (h ≫ pD) (𝟙 S) h (Category.comp_id _))
        (moduleDerivedLowerShriekCartesianBaseChangeIso (𝟙 X) jC jD h sq.flip Λ))
      (moduleDerivedInverseImageIdIso Λ S)
      (moduleDerivedInverseImageIdIso Λ X)
      (moduleDerivedProperRefinementComparison jC jD h sq Λ)
      (moduleDerivedDirectImageCompIso Λ pD h) :=
  compactifiedIdentityBaseEquation
    (moduleDerivedAdjunction Λ h) (moduleDerivedDirectImageCompIso Λ pD h)
    (moduleDerivedInverseImageIdIso Λ S) (moduleDerivedInverseImageIdIso Λ X)
    (moduleDerivedBaseChangeMap Λ pD (h ≫ pD) (𝟙 S) h (Category.comp_id _))
    (moduleDerivedLowerShriekCartesianBaseChangeIso (𝟙 X) jC jD h sq.flip Λ)
    (moduleDerivedProperRefinementPullbackIso jC jD h sq Λ)
    (moduleDerivedProperRefinementComparison jC jD h sq Λ)
    (moduleDerivedBaseChangeMap_composite_id_unit Λ pD h)
    (moduleDerivedLowerShriekCartesianBaseChangeIso_identity_source jC jD h sq.flip Λ).symm
    (moduleDerivedProperRefinementComparison_app jC jD h sq Λ)
    _ rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
