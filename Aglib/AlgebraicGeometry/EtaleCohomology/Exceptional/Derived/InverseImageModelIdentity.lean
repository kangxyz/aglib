/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.IdentityModelComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Composition

/-!
# Actual inverse image of the identity with independent base derived models

This is the existing native change-target comparison followed by the original
same-model inverse-image identity. Its unit formula retains the original
ordinary identity and canonical quotient comparison. No equality of models is used.
-/

@[expose] public noncomputable section
open CategoryTheory DerivedCategory.Plus
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u d₀ d₁
variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
  (h₀ : HasDerivedCategory.{d₀} (ModuleSheaf X Λ))
  (h₁ : HasDerivedCategory.{d₁} (ModuleSheaf X Λ))

/-- The actual native inverse image of the scheme identity is canonical model transport. -/
def moduleDerivedInverseImageModelIdIso :
    (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ h₀ h₁ (moduleInverseImage (𝟙 X) Λ) _ _) ≅
      (canonicalEquivalence h₀ h₁).functor :=
  Functor.rightDerivedFunctorPlusIdentityModelIso h₀ h₁
    (moduleInverseImage (𝟙 X) Λ) (moduleInverseImageIdIso Λ X)

/-- Original quotient/unit normalization of the actual identity inverse image. -/
@[reassoc]
theorem moduleDerivedInverseImageModelIdIso_unit (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    ((@Functor.rightDerivedFunctorPlusUnit _ _ _ _ _ _ h₀ h₁ (moduleInverseImage (𝟙 X) Λ) _
      _)).app K ≫
        (moduleDerivedInverseImageModelIdIso X Λ h₀ h₁).hom.app (((@DerivedCategory.Plus.Q _ _ _
          h₀)).obj K) ≫
        (quotientCompCanonicalEquivalenceIso h₀ h₁).hom.app K =
      ((@DerivedCategory.Plus.Q _ _ _ h₁)).map ((NatIso.mapCochainComplexPlus
        (moduleInverseImageIdIso Λ X)).hom.app K ≫
        (Functor.mapCochainComplexPlusIdIso (ModuleSheaf X Λ)).hom.app K) :=
  Functor.rightDerivedFunctorPlusIdentityModelIso_unit h₀ h₁
    (moduleInverseImage (𝟙 X) Λ) (moduleInverseImageIdIso Λ X) K

end AlgebraicGeometry.Scheme.EtaleCohomology
