/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.LowerShriekComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralComparisons
public import
  Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactAdjunctionIdentity
public import Aglib.CategoryTheory.Adjunction.LeftAdjointComparison

/-!
# Original unbounded lower-shriek and inverse-image identity conjugacy

The original localized lower-shriek identity is conjugate to the original
inverse-image identity under the installed exact unbounded adjunction.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX

variable (Λ : Type (u + 1)) [Ring Λ]

/-- The native unbounded identity maps retain the original adjunction unit. -/
theorem conjugateEquiv_moduleUnboundedDerivedLowerShriekIdIso_hom
    (X : Scheme.{u}) [HasDerivedCategory.{wX} (ModuleSheaf X Λ)] :
    conjugateEquiv Adjunction.id (moduleUnboundedDerivedLowerShriekAdjunction (𝟙 X) Λ)
      (moduleUnboundedDerivedLowerShriekIdIso Λ X).hom =
      (moduleUnboundedDerivedInverseImageIdIso Λ X).inv :=
  Adjunction.mapDerivedCategory_conjugate_id (moduleLowerShriekAdjunction (𝟙 X) Λ)
    (moduleLowerShriekIdIso Λ X) (moduleInverseImageIdIso Λ X)
    (conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
      (moduleLowerShriekAdjunction (𝟙 X) Λ) Adjunction.id (moduleInverseImageIdIso Λ X))

end AlgebraicGeometry.Scheme.EtaleCohomology
