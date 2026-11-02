/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.UnboundedComplex
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ClosedExactness
public import Aglib.CategoryTheory.Functor.ComparisonPasting.LocalizationVertices

/-!
# The original unbounded derived vertices of module localization

The first vertex is identified with the installed exact open composite using
its original localization factors. Exactness of closed direct image makes its
actual unbounded right-derived unit invertible and identifies the third vertex
with the installed closed composite. The resulting first and second arrows
are the original unbounded adjunction counit and unit, not arbitrary maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wU wZ wX

variable {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (Λ : Type (u + 1)) [Ring Λ] (i : Z ⟶ X) [IsClosedImmersion i]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- Closed direct-image exactness makes its original unbounded derived unit invertible. -/
instance moduleClosedUnboundedDerivedDirectImageUnit_isIso :
    IsIso (moduleUnboundedDerivedDirectImageUnit Λ i) := by
  apply Functor.isIso_of_isRightDerivedFunctor_of_inverts
    (W := HomologicalComplex.quasiIso (ModuleSheaf Z Λ) (.up ℤ))
    (moduleUnboundedDerivedDirectImage Λ i) (moduleUnboundedDerivedDirectImageUnit Λ i)
  intro K L a ha
  have : QuasiIso a := ha
  change IsIso (DerivedCategory.Q.map
    (((moduleDirectImage i Λ).mapHomologicalComplex (.up ℤ)).map a))
  infer_instance

/-- The whole open comparison uses the two installed exact localization factors. -/
def moduleUnboundedLocalizationFirstVertexNatIso :
    (moduleInverseImage j Λ).mapHomologicalComplex (.up ℤ) ⋙
        (moduleLowerShriek j Λ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ moduleUnboundedDerivedInverseImage Λ j ⋙
        moduleUnboundedDerivedLowerShriek j Λ :=
  Functor.compositeLocalizationIso
    (moduleLowerShriek j Λ).mapDerivedCategoryFactors.symm
    (moduleInverseImage j Λ).mapDerivedCategoryFactors.symm

/-- The whole closed comparison uses the original unbounded direct-image unit. -/
def moduleUnboundedLocalizationThirdVertexNatIso :
    (moduleInverseImage i Λ).mapHomologicalComplex (.up ℤ) ⋙
        (moduleDirectImage i Λ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ moduleUnboundedDerivedInverseImage Λ i ⋙
        moduleUnboundedDerivedDirectImage Λ i :=
  Functor.compositeLocalizationIso (asIso (moduleUnboundedDerivedDirectImageUnit Λ i))
    (moduleInverseImage i Λ).mapDerivedCategoryFactors.symm

/-- The open vertex uses precisely the two installed exact localization factors. -/
def moduleUnboundedLocalizationFirstVertexIso (K : CochainComplex (ModuleSheaf X Λ) ℤ) :
    DerivedCategory.Q.obj (((moduleLowerShriek j Λ).mapHomologicalComplex (.up ℤ)).obj
      (((moduleInverseImage j Λ).mapHomologicalComplex (.up ℤ)).obj K)) ≅
    (moduleUnboundedDerivedLowerShriek j Λ).obj
      ((moduleUnboundedDerivedInverseImage Λ j).obj (DerivedCategory.Q.obj K)) :=
  (moduleUnboundedLocalizationFirstVertexNatIso j Λ).app K

/-- The closed vertex uses its original unbounded right-derived unit. -/
def moduleUnboundedLocalizationThirdVertexIso (K : CochainComplex (ModuleSheaf X Λ) ℤ) :
    DerivedCategory.Q.obj (((moduleDirectImage i Λ).mapHomologicalComplex (.up ℤ)).obj
      (((moduleInverseImage i Λ).mapHomologicalComplex (.up ℤ)).obj K)) ≅
    (moduleUnboundedDerivedDirectImage Λ i).obj
      ((moduleUnboundedDerivedInverseImage Λ i).obj (DerivedCategory.Q.obj K)) :=
  (moduleUnboundedLocalizationThirdVertexNatIso Λ i).app K

/-- The open vertex comparison identifies the original cochain counit exactly. -/
theorem moduleUnboundedLocalizationFirstVertexIso_counit
    (K : CochainComplex (ModuleSheaf X Λ) ℤ) :
    (moduleUnboundedLocalizationFirstVertexIso j Λ K).hom ≫
      (moduleUnboundedDerivedLowerShriekAdjunction j Λ).counit.app (DerivedCategory.Q.obj K) =
    DerivedCategory.Q.map
      (((moduleLowerShriekAdjunction j Λ).mapHomologicalComplex (.up ℤ)).counit.app K) := by
  exact Functor.compositeLocalizationIso_counit_of_formula
    (moduleLowerShriek j Λ).mapDerivedCategoryFactors.symm
    (moduleInverseImage j Λ).mapDerivedCategoryFactors.symm
    ((moduleLowerShriekAdjunction j Λ).mapHomologicalComplex (.up ℤ)).counit
    (moduleUnboundedDerivedLowerShriekAdjunction j Λ).counit
    (moduleUnboundedDerivedLowerShriekAdjunction_counit_app j Λ) K

/-- The closed vertex comparison identifies the original cochain unit exactly. -/
theorem moduleUnboundedLocalizationThirdVertexIso_unit
    (K : CochainComplex (ModuleSheaf X Λ) ℤ) :
    DerivedCategory.Q.map
        (((moduleInverseImageAdjunction i Λ).mapHomologicalComplex (.up ℤ)).unit.app K) ≫
      (moduleUnboundedLocalizationThirdVertexIso Λ i K).hom =
    (moduleUnboundedDerivedAdjunction Λ i).unit.app (DerivedCategory.Q.obj K) := by
  exact Functor.compositeLocalizationIso_unit
    (asIso (moduleUnboundedDerivedDirectImageUnit Λ i))
    (moduleInverseImage i Λ).mapDerivedCategoryFactors.symm
    ((moduleInverseImageAdjunction i Λ).mapHomologicalComplex (.up ℤ)).unit
    (moduleUnboundedDerivedAdjunction Λ i).unit
    (moduleUnboundedDerivedAdjunction_unit_fac Λ i) K

/-- The exact open-vertex comparison is natural for every original complex map. -/
@[reassoc]
theorem moduleUnboundedLocalizationFirstVertexIso_naturality
    {K L : CochainComplex (ModuleSheaf X Λ) ℤ} (a : K ⟶ L) :
    DerivedCategory.Q.map (((moduleLowerShriek j Λ).mapHomologicalComplex (.up ℤ)).map
        (((moduleInverseImage j Λ).mapHomologicalComplex (.up ℤ)).map a)) ≫
      (moduleUnboundedLocalizationFirstVertexIso j Λ L).hom =
    (moduleUnboundedLocalizationFirstVertexIso j Λ K).hom ≫
      (moduleUnboundedDerivedLowerShriek j Λ).map
        ((moduleUnboundedDerivedInverseImage Λ j).map (DerivedCategory.Q.map a)) :=
  (moduleUnboundedLocalizationFirstVertexNatIso j Λ).hom.naturality a

/-- The original closed-unit comparison is natural for every original complex map. -/
@[reassoc]
theorem moduleUnboundedLocalizationThirdVertexIso_naturality
    {K L : CochainComplex (ModuleSheaf X Λ) ℤ} (a : K ⟶ L) :
    DerivedCategory.Q.map (((moduleDirectImage i Λ).mapHomologicalComplex (.up ℤ)).map
        (((moduleInverseImage i Λ).mapHomologicalComplex (.up ℤ)).map a)) ≫
      (moduleUnboundedLocalizationThirdVertexIso Λ i L).hom =
    (moduleUnboundedLocalizationThirdVertexIso Λ i K).hom ≫
      (moduleUnboundedDerivedDirectImage Λ i).map
        ((moduleUnboundedDerivedInverseImage Λ i).map (DerivedCategory.Q.map a)) :=
  (moduleUnboundedLocalizationThirdVertexNatIso Λ i).hom.naturality a

end AlgebraicGeometry.Scheme.EtaleCohomology
