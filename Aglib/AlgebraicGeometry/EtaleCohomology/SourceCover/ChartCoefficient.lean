/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleAdjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Genuine original coefficients on source charts

The original module inverse image preserves genuine injectivity by the native
exact etale lower-shriek adjunction. The original underlying comparison and
inverse-image square identify the actual pulled chart coefficient, without
assuming scalar-forgotten injectivity or replacing a resolution.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules

/-- Genuine ringed injectivity survives original etale source-chart restriction. -/
theorem sourceChartModule_injective {X : Scheme.{u}} (U : X.Etale)
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf X Λ) [Injective I] :
    Injective ((moduleInverseImage U.hom Λ).obj I) := by
  let : (moduleInverseImage U.hom Λ).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (moduleLowerShriekAdjunction U.hom Λ)
  infer_instance

/-- The original module restriction and actual cartesian inverse-image square
return exactly the original coefficient on the literal pulled-back etale chart. -/
def sourceChartModuleCoefficientIso {X X' : Scheme.{u}} (g' : X' ⟶ X) (U : X.Etale)
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf X Λ) :
    (inverseImage (pullback.fst U.hom g')).obj
        ((SheafOfModules.toSheaf (constantRing U.left Λ)).obj
          ((moduleInverseImage U.hom Λ).obj I)) ≅
      (inverseImage ((siteBaseChange g').obj U).hom).obj
        ((inverseImage g').obj ((SheafOfModules.toSheaf (constantRing X Λ)).obj I)) :=
  (inverseImage (pullback.fst U.hom g')).mapIso
      ((moduleInverseImageUnderlyingIso Λ U.hom).app I) ≪≫
    (inverseImageSquareIso U.hom ((siteBaseChange g').obj U).hom g'
      (pullback.fst U.hom g') pullback.condition.symm).symm.app
        ((SheafOfModules.toSheaf (constantRing X Λ)).obj I)

end AlgebraicGeometry.Scheme.EtaleCohomology
