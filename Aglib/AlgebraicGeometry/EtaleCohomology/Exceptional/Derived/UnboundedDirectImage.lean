/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.DirectImage
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Comparison
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ExactFunctor

/-!
# Native unbounded direct images for constant-ring modules

The actual Grothendieck category of constant-ring module sheaves on the original
small-etale site admits the constructed K-injective replacement. Its unbounded
direct image is therefore the native right-derived functor, with no replacement
premise. The original exact inverse image induces its left adjoint on the same
native derived categories. Both adjunction equations and the bounded-below
comparisons retain the original localization maps.

These are ordinary derived images for arbitrary coefficient rings. Neither a
torsion hypothesis nor a Noetherian or base-invertibility assumption is used.
This leaf does not assert proper base change or exceptional-image independence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u w w'

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable (Λ : Type (u + 1)) [Ring Λ] {X S : Scheme.{u}} (f : S ⟶ X)
  [HasDerivedCategory.{w} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{w'} (ModuleSheaf S Λ)]

/-- The native localization of the original exact constant-ring inverse image. -/
abbrev moduleUnboundedDerivedInverseImage :
    DerivedCategory (ModuleSheaf X Λ) ⥤ DerivedCategory (ModuleSheaf S Λ) :=
  (moduleInverseImage f Λ).mapDerivedCategory

/-- The actual unbounded right-derived functor of the original ringed direct image. -/
abbrev moduleUnboundedDerivedDirectImage :
    DerivedCategory (ModuleSheaf S Λ) ⥤ DerivedCategory (ModuleSheaf X Λ) :=
  (moduleDirectImage f Λ).unboundedRightDerivedFunctor

/-- The original localization unit of the actual unbounded direct image. -/
abbrev moduleUnboundedDerivedDirectImageUnit :
    (moduleDirectImage f Λ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ moduleUnboundedDerivedDirectImage Λ f :=
  (moduleDirectImage f Λ).unboundedRightDerivedFunctorUnit

/-- Computation by any genuine K-injective resolution of the original complex. -/
abbrev moduleUnboundedDerivedDirectImageObjIso
    {K I : CochainComplex (ModuleSheaf S Λ) ℤ} (i : K ⟶ I) [QuasiIso i]
    [I.IsKInjective] :
    (moduleUnboundedDerivedDirectImage Λ f).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (((moduleDirectImage f Λ).mapHomologicalComplex (.up ℤ)).obj I) :=
  (moduleDirectImage f Λ).unboundedRightDerivedFunctorObjIso i

/-- The computation comparison retains the specified original resolution map. -/
@[reassoc]
theorem moduleUnboundedDerivedDirectImageUnit_app_comp_objIso_hom
    {K I : CochainComplex (ModuleSheaf S Λ) ℤ} (i : K ⟶ I) [QuasiIso i]
    [I.IsKInjective] :
    (moduleUnboundedDerivedDirectImageUnit Λ f).app K ≫
      (moduleUnboundedDerivedDirectImageObjIso Λ f i).hom =
    DerivedCategory.Q.map (((moduleDirectImage f Λ).mapHomologicalComplex (.up ℤ)).map i) :=
  (moduleDirectImage f Λ).unboundedRightDerivedFunctorUnit_app_comp_objIso_hom i

/-- The original ringed adjunction induces the actual native unbounded adjunction. -/
abbrev moduleUnboundedDerivedAdjunction :
    moduleUnboundedDerivedInverseImage Λ f ⊣ moduleUnboundedDerivedDirectImage Λ f :=
  (moduleInverseImageAdjunction f Λ).unboundedRightDerivedAdjunction

/-- The unbounded derived unit is induced by the original cochain adjunction unit. -/
@[reassoc]
theorem moduleUnboundedDerivedAdjunction_unit_fac
    (K : CochainComplex (ModuleSheaf X Λ) ℤ) :
    (moduleUnboundedDerivedAdjunction Λ f).unit.app (DerivedCategory.Q.obj K) ≫
      (moduleUnboundedDerivedDirectImage Λ f).map
        ((moduleInverseImage f Λ).mapDerivedCategoryFactors.hom.app K) =
    DerivedCategory.Q.map
        (((moduleInverseImageAdjunction f Λ).mapHomologicalComplex (.up ℤ)).unit.app K) ≫
      (moduleUnboundedDerivedDirectImageUnit Λ f).app
        (((moduleInverseImage f Λ).mapHomologicalComplex (.up ℤ)).obj K) :=
  (moduleInverseImageAdjunction f Λ).unboundedRightDerivedAdjunction_unit_app K

/-- The unbounded derived counit retains the original cochain adjunction counit. -/
@[reassoc]
theorem moduleUnboundedDerivedAdjunction_counit_fac
    (K : CochainComplex (ModuleSheaf S Λ) ℤ) :
    (moduleUnboundedDerivedInverseImage Λ f).map
        ((moduleUnboundedDerivedDirectImageUnit Λ f).app K) ≫
      (moduleUnboundedDerivedAdjunction Λ f).counit.app (DerivedCategory.Q.obj K) =
    (moduleInverseImage f Λ).mapDerivedCategoryFactors.hom.app
        (((moduleDirectImage f Λ).mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        (((moduleInverseImageAdjunction f Λ).mapHomologicalComplex (.up ℤ)).counit.app K) :=
  (moduleInverseImageAdjunction f Λ).unboundedRightDerivedAdjunction_counit_app K

/-- The canonical comparison from the existing bounded-below direct image. -/
abbrev moduleDerivedDirectImageCompιIso :
    moduleDerivedDirectImage Λ f ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ moduleUnboundedDerivedDirectImage Λ f :=
  (moduleDirectImage f Λ).unboundedRightDerivedFunctorPlusIso

/-- The bounded-below direct-image comparison preserves the original derived units. -/
@[reassoc]
theorem moduleDerivedDirectImageCompιIso_unit_app
    (K : CochainComplex.Plus (ModuleSheaf S Λ)) :
    DerivedCategory.Plus.ι.map ((moduleDirectImage f Λ).rightDerivedFunctorPlusUnit.app K) ≫
      (moduleDerivedDirectImageCompιIso Λ f).hom.app (DerivedCategory.Plus.Q.obj K) =
    (moduleUnboundedDerivedDirectImageUnit Λ f).app K.obj :=
  (moduleDirectImage f Λ).unboundedRightDerivedFunctorPlusIso_unit_app K

/-- The canonical comparison from the existing bounded-below inverse image. -/
abbrev moduleDerivedInverseImageCompιIso :
    moduleDerivedInverseImage Λ f ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ moduleUnboundedDerivedInverseImage Λ f :=
  (moduleInverseImage f Λ).rightDerivedFunctorPlusCompιIso

/-- The inverse-image comparison retains the original exact localization factor. -/
@[reassoc]
theorem moduleDerivedInverseImageCompιIso_unit_app
    (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    DerivedCategory.Plus.ι.map ((moduleInverseImage f Λ).rightDerivedFunctorPlusUnit.app K) ≫
      (moduleDerivedInverseImageCompιIso Λ f).hom.app (DerivedCategory.Plus.Q.obj K) =
    (moduleInverseImage f Λ).mapDerivedCategoryFactors.inv.app K.obj := by
  simpa using (moduleInverseImage f Λ).rightDerivedFunctorPlusCompιIso_unit K

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
