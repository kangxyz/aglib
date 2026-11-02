/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenToDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.LowerShriekIdentityConjugacy
public import Aglib.CategoryTheory.Adjunction.TripleIdentity

/-! # Original identity value of the unbounded outer-adjoint comparison -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX
variable (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u})
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- The actual canonical open map at the identity retains both original identity maps. -/
theorem moduleUnboundedLowerShriekToDirectImage_id :
    moduleUnboundedLowerShriekToDirectImage Λ (𝟙 X) =
      (moduleUnboundedDerivedLowerShriekIdIso Λ X).hom ≫
        (moduleUnboundedDerivedDirectImageIdIso Λ X).inv :=
  Adjunction.Triple.leftToRight_identity (moduleUnboundedOpenTriple Λ (𝟙 X))
    (moduleUnboundedDerivedLowerShriekIdIso Λ X)
    (moduleUnboundedDerivedInverseImageIdIso Λ X)
    (moduleUnboundedDerivedDirectImageIdIso Λ X)
    (conjugateEquiv_moduleUnboundedDerivedLowerShriekIdIso_hom Λ X)
    (conjugateEquiv_moduleUnboundedDerivedInverseImageIdIso_hom Λ X)

end AlgebraicGeometry.Scheme.EtaleCohomology
