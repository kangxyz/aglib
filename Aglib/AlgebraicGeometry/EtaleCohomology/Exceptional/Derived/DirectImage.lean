/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Exactness
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Size
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction

/-!
# Native bounded-below direct images for constant-ring modules

The existing large-value module-sheaf Grothendieck theorem supplies enough
injectives on the original site. The native exact pullback/direct-image
adjunction then gives the installed bounded-below derived adjunction. Its
unit retains the original localization equation. This is an ordinary derived
image supplier, not exceptional-image independence or proper base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u w w'

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]

/-- Grothendieck structure on the actual constant-ring module-sheaf category. -/
instance moduleSheaf_isGrothendieckAbelian :
    IsGrothendieckAbelian.{u + 1} (ModuleSheaf X Λ) :=
  SheafOfModules.isGrothendieckAbelianLarge.{u + 1, u, 0} (constantRing X Λ)

/-- Enough injectives on the original site, without a small-site replacement. -/
instance moduleSheaf_enoughInjectives : EnoughInjectives (ModuleSheaf X Λ) := by
  infer_instance

variable {X} {S : Scheme.{u}} (f : S ⟶ X)
  [HasDerivedCategory.{w} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{w'} (ModuleSheaf S Λ)]

/-- The installed bounded-below derived functor of the native exact pullback. -/
abbrev moduleDerivedInverseImage :
    DerivedCategory.Plus (ModuleSheaf X Λ) ⥤
      DerivedCategory.Plus (ModuleSheaf S Λ) :=
  (moduleInverseImage f Λ).rightDerivedFunctorPlus

/-- The installed bounded-below derived functor of the genuine ringed direct image. -/
abbrev moduleDerivedDirectImage :
    DerivedCategory.Plus (ModuleSheaf S Λ) ⥤
      DerivedCategory.Plus (ModuleSheaf X Λ) :=
  (moduleDirectImage f Λ).rightDerivedFunctorPlus

/-- The original ringed adjunction induces the native bounded-below adjunction. -/
def moduleDerivedAdjunction :
    moduleDerivedInverseImage Λ f ⊣ moduleDerivedDirectImage Λ f :=
  (moduleInverseImageAdjunction f Λ).rightDerivedFunctorPlus

/-- The native derived unit retains the original complex-adjunction unit. -/
@[reassoc]
theorem moduleDerivedAdjunction_unit_fac (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    (moduleDerivedAdjunction Λ f).unit.app (DerivedCategory.Plus.Q.obj K) ≫
      (moduleDerivedDirectImage Λ f).map
        ((moduleInverseImage f Λ).rightDerivedFunctorPlusExactComparison.hom.app K) =
    DerivedCategory.Plus.Q.map
        ((moduleInverseImageAdjunction f Λ).mapCochainComplexPlus.unit.app K) ≫
      (moduleDirectImage f Λ).rightDerivedFunctorPlusUnit.app
        ((moduleInverseImage f Λ).mapCochainComplexPlus.obj K) :=
  (moduleInverseImageAdjunction f Λ).rightDerivedFunctorPlus_unit_fac K

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
