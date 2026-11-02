/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.ToDirectImageCompatibility
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.LowerShriekComposition
public import Aglib.CategoryTheory.Adjunction.TripleIdentity

/-! # Same-model identity normalization of the original canonical `j! → Rj*`

This theorem deliberately uses one fixed model. It does not identify an
independent middle model in an identity factorization.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u w
variable (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u})
  [HasDerivedCategory.{w} (ModuleSheaf X Λ)]

/-- The canonical triple map at identity is normalized by both original identity isomorphisms. -/
theorem moduleDerivedLowerShriekToDirectImage_id :
    moduleDerivedLowerShriekToDirectImage Λ (𝟙 X) =
      (moduleDerivedLowerShriekIdIso Λ X).hom ≫ (moduleDerivedDirectImageIdIso Λ X).inv :=
  Adjunction.Triple.leftToRight_identity (moduleDerivedOpenTriple Λ (𝟙 X))
    (moduleDerivedLowerShriekIdIso Λ X) (moduleDerivedInverseImageIdIso Λ X)
    (moduleDerivedDirectImageIdIso Λ X)
    (conjugateEquiv_moduleDerivedLowerShriekIdIso_hom Λ X)
    (conjugateEquiv_moduleDerivedInverseImageIdIso_hom Λ X)

end AlgebraicGeometry.Scheme.EtaleCohomology
