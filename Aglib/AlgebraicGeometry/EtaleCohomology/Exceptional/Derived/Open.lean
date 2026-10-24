/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.DirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleAdjunction

/-!
# Native bounded-below module lower shriek

The actual exact module extension and its original inverse-image adjunction
induce the installed bounded-below adjunction. Its unit and counit retain the
original complex maps. No compactification choice, proper base change, or
unbounded replacement is assumed here.
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

instance moduleLowerShriek_preservesHomology : (moduleLowerShriek j Λ).PreservesHomology := by
  infer_instance

/-- The installed bounded-below functor of the genuine exact module lower shriek. -/
abbrev moduleDerivedLowerShriek :
    DerivedCategory.Plus (ModuleSheaf U Λ) ⥤
      DerivedCategory.Plus (ModuleSheaf X Λ) :=
  (moduleLowerShriek j Λ).rightDerivedFunctorPlus

/-- The bounded-below adjunction retains the native module inverse image. -/
def moduleDerivedLowerShriekAdjunction :
    moduleDerivedLowerShriek j Λ ⊣ moduleDerivedInverseImage Λ j :=
  (moduleLowerShriekAdjunction j Λ).rightDerivedFunctorPlus

/-- The derived lower-shriek unit factors through the original unit of complexes. -/
@[reassoc]
theorem moduleDerivedLowerShriekAdjunction_unit_fac
    (K : CochainComplex.Plus (ModuleSheaf U Λ)) :
    (moduleDerivedLowerShriekAdjunction j Λ).unit.app (DerivedCategory.Plus.Q.obj K) ≫
      (moduleDerivedInverseImage Λ j).map
        ((moduleLowerShriek j Λ).rightDerivedFunctorPlusExactComparison.hom.app K) =
    DerivedCategory.Plus.Q.map
        ((moduleLowerShriekAdjunction j Λ).mapCochainComplexPlus.unit.app K) ≫
      (moduleInverseImage j Λ).rightDerivedFunctorPlusUnit.app
        ((moduleLowerShriek j Λ).mapCochainComplexPlus.obj K) :=
  (moduleLowerShriekAdjunction j Λ).rightDerivedFunctorPlus_unit_fac K

/-- The derived lower-shriek counit retains the original counit of complexes. -/
@[reassoc]
theorem moduleDerivedLowerShriekAdjunction_counit_fac
    (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    (moduleDerivedLowerShriek j Λ).map
        ((moduleInverseImage j Λ).rightDerivedFunctorPlusUnit.app K) ≫
      (moduleDerivedLowerShriekAdjunction j Λ).counit.app (DerivedCategory.Plus.Q.obj K) =
    (moduleLowerShriek j Λ).rightDerivedFunctorPlusExactComparison.hom.app
        ((moduleInverseImage j Λ).mapCochainComplexPlus.obj K) ≫
      DerivedCategory.Plus.Q.map
        ((moduleLowerShriekAdjunction j Λ).mapCochainComplexPlus.counit.app K) :=
  (moduleLowerShriekAdjunction j Λ).rightDerivedFunctorPlus_counit_fac K

end AlgebraicGeometry.Scheme.EtaleCohomology
