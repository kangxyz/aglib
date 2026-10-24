/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnboundedDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Open
public import Mathlib.CategoryTheory.Localization.Adjunction

/-!
# Native unbounded module extension by zero

The genuine exact module lower shriek induces the native functor on unbounded
derived categories. The original cochain adjunction descends by localization,
with the same exact inverse image used by the unbounded direct-image adjunction.
Its unit and counit are expressed by the original chain maps and the installed
localization factors. The canonical comparison with the existing bounded-below
lower shriek preserves its original localization unit.

The construction applies to etale morphisms; in particular it is extension by
zero for open immersions. It does not use proper base change and does not yet
identify an unbounded open-closed localization triangle.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u w w'

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{w} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{w'} (ModuleSheaf X Λ)]

/-- The native unbounded derived functor of the genuine exact module lower shriek. -/
abbrev moduleUnboundedDerivedLowerShriek :
    DerivedCategory (ModuleSheaf U Λ) ⥤ DerivedCategory (ModuleSheaf X Λ) :=
  (moduleLowerShriek j Λ).mapDerivedCategory

/-- The actual exact lower-shriek factor supplies the localization square. -/
local instance lowerShriekLocalizationSquare :
    CatCommSq ((moduleLowerShriek j Λ).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (moduleUnboundedDerivedLowerShriek j Λ) :=
  ⟨(moduleLowerShriek j Λ).mapDerivedCategoryFactors.symm⟩

/-- The same original exact inverse-image factor supplies the other square. -/
local instance inverseImageLocalizationSquare :
    CatCommSq ((moduleInverseImage j Λ).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (moduleUnboundedDerivedInverseImage Λ j) :=
  ⟨(moduleInverseImage j Λ).mapDerivedCategoryFactors.symm⟩

/-- The original exact lower-shriek adjunction descends to the native derived categories. -/
def moduleUnboundedDerivedLowerShriekAdjunction :
    moduleUnboundedDerivedLowerShriek j Λ ⊣ moduleUnboundedDerivedInverseImage Λ j :=
  ((moduleLowerShriekAdjunction j Λ).mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso (ModuleSheaf U Λ) (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ))
    (moduleUnboundedDerivedLowerShriek j Λ) (moduleUnboundedDerivedInverseImage Λ j)

/-- The unbounded lower-shriek unit is the localized original cochain unit. -/
@[reassoc]
theorem moduleUnboundedDerivedLowerShriekAdjunction_unit_app
    (K : CochainComplex (ModuleSheaf U Λ) ℤ) :
    (moduleUnboundedDerivedLowerShriekAdjunction j Λ).unit.app (DerivedCategory.Q.obj K) =
    DerivedCategory.Q.map
        (((moduleLowerShriekAdjunction j Λ).mapHomologicalComplex (.up ℤ)).unit.app K) ≫
      (moduleInverseImage j Λ).mapDerivedCategoryFactors.inv.app
        (((moduleLowerShriek j Λ).mapHomologicalComplex (.up ℤ)).obj K) ≫
      (moduleUnboundedDerivedInverseImage Λ j).map
        ((moduleLowerShriek j Λ).mapDerivedCategoryFactors.inv.app K) :=
  ((moduleLowerShriekAdjunction j Λ).mapHomologicalComplex (.up ℤ)).localization_unit_app
    DerivedCategory.Q (HomologicalComplex.quasiIso (ModuleSheaf U Λ) (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ))
    (moduleUnboundedDerivedLowerShriek j Λ) (moduleUnboundedDerivedInverseImage Λ j) K

/-- The unbounded lower-shriek counit retains the original cochain counit. -/
@[reassoc]
theorem moduleUnboundedDerivedLowerShriekAdjunction_counit_app
    (K : CochainComplex (ModuleSheaf X Λ) ℤ) :
    (moduleUnboundedDerivedLowerShriekAdjunction j Λ).counit.app (DerivedCategory.Q.obj K) =
    (moduleUnboundedDerivedLowerShriek j Λ).map
        ((moduleInverseImage j Λ).mapDerivedCategoryFactors.hom.app K) ≫
      (moduleLowerShriek j Λ).mapDerivedCategoryFactors.hom.app
        (((moduleInverseImage j Λ).mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        (((moduleLowerShriekAdjunction j Λ).mapHomologicalComplex (.up ℤ)).counit.app K) :=
  ((moduleLowerShriekAdjunction j Λ).mapHomologicalComplex (.up ℤ)).localization_counit_app
    DerivedCategory.Q (HomologicalComplex.quasiIso (ModuleSheaf U Λ) (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso (ModuleSheaf X Λ) (.up ℤ))
    (moduleUnboundedDerivedLowerShriek j Λ) (moduleUnboundedDerivedInverseImage Λ j) K

/-- The canonical comparison from the existing bounded-below module lower shriek. -/
abbrev moduleDerivedLowerShriekCompιIso :
    moduleDerivedLowerShriek j Λ ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ moduleUnboundedDerivedLowerShriek j Λ :=
  (moduleLowerShriek j Λ).rightDerivedFunctorPlusCompιIso

/-- The bounded-below comparison retains the original exact localization factor. -/
@[reassoc]
theorem moduleDerivedLowerShriekCompιIso_unit_app
    (K : CochainComplex.Plus (ModuleSheaf U Λ)) :
    DerivedCategory.Plus.ι.map ((moduleLowerShriek j Λ).rightDerivedFunctorPlusUnit.app K) ≫
      (moduleDerivedLowerShriekCompιIso j Λ).hom.app (DerivedCategory.Plus.Q.obj K) =
    (moduleLowerShriek j Λ).mapDerivedCategoryFactors.inv.app K.obj := by
  simpa using (moduleLowerShriek j Λ).rightDerivedFunctorPlusCompιIso_unit K

end AlgebraicGeometry.Scheme.EtaleCohomology
