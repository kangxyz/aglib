/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ModuleComplex
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ClosedExactness

/-!
# The actual derived vertices of module localization

The native short-exact-complex triangle is compared with the separately
installed derived lower shriek, inverse image, and direct image. Both vertex
comparisons use the original derived units. The first two triangle arrows
are exactly the original derived adjunction counit and unit.
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

/-- The first vertex uses the exact-left comparison and original inverse-image derived unit. -/
def moduleLocalizationFirstVertexIso (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    DerivedCategory.Plus.Q.obj ((moduleLowerShriek j Λ).mapCochainComplexPlus.obj
      ((moduleInverseImage j Λ).mapCochainComplexPlus.obj K)) ≅
    (moduleDerivedLowerShriek j Λ).obj
      ((moduleDerivedInverseImage Λ j).obj (DerivedCategory.Plus.Q.obj K)) := by
  let : IsIso (moduleInverseImage j Λ).rightDerivedFunctorPlusUnit :=
    (moduleInverseImage j Λ).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  exact ((moduleLowerShriek j Λ).rightDerivedFunctorPlusExactComparison.app
      ((moduleInverseImage j Λ).mapCochainComplexPlus.obj K)).symm ≪≫
    (moduleDerivedLowerShriek j Λ).mapIso
      (asIso ((moduleInverseImage j Λ).rightDerivedFunctorPlusUnit.app K))

/-- The third vertex is the actual separately derived closed direct image and inverse image. -/
def moduleLocalizationThirdVertexIso (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    DerivedCategory.Plus.Q.obj ((moduleDirectImage i Λ).mapCochainComplexPlus.obj
      ((moduleInverseImage i Λ).mapCochainComplexPlus.obj K)) ≅
    (moduleDerivedDirectImage Λ i).obj
      ((moduleDerivedInverseImage Λ i).obj (DerivedCategory.Plus.Q.obj K)) := by
  let : IsIso (moduleDirectImage i Λ).rightDerivedFunctorPlusUnit :=
    (moduleDirectImage i Λ).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  exact asIso ((moduleDirectImage i Λ).rightDerivedFunctorPlusUnit.app
      ((moduleInverseImage i Λ).mapCochainComplexPlus.obj K)) ≪≫
    (moduleDerivedDirectImage Λ i).mapIso
      ((moduleInverseImage i Λ).rightDerivedFunctorPlusExactComparison.app K).symm

/-- The first comparison identifies the original complex counit with the derived counit. -/
theorem moduleLocalizationFirstVertexIso_counit
    (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    (moduleLocalizationFirstVertexIso j Λ K).hom ≫
      (moduleDerivedLowerShriekAdjunction j Λ).counit.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
      ((moduleLowerShriekAdjunction j Λ).mapCochainComplexPlus.counit.app K) := by
  change ((moduleLowerShriek j Λ).rightDerivedFunctorPlusExactComparison.inv.app
      ((moduleInverseImage j Λ).mapCochainComplexPlus.obj K) ≫
      (moduleDerivedLowerShriek j Λ).map
        ((moduleInverseImage j Λ).rightDerivedFunctorPlusUnit.app K)) ≫ _ = _
  rw [Category.assoc, moduleDerivedLowerShriekAdjunction_counit_fac,
    ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- The third comparison identifies the original complex unit with the derived unit. -/
theorem moduleLocalizationThirdVertexIso_unit
    (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    DerivedCategory.Plus.Q.map
        ((moduleInverseImageAdjunction i Λ).mapCochainComplexPlus.unit.app K) ≫
      (moduleLocalizationThirdVertexIso Λ i K).hom =
    (moduleDerivedAdjunction Λ i).unit.app (DerivedCategory.Plus.Q.obj K) := by
  change _ ≫ ((moduleDirectImage i Λ).rightDerivedFunctorPlusUnit.app
      ((moduleInverseImage i Λ).mapCochainComplexPlus.obj K) ≫
      (moduleDerivedDirectImage Λ i).map
        ((moduleInverseImage i Λ).rightDerivedFunctorPlusExactComparison.inv.app K)) = _
  rw [← Category.assoc, ← moduleDerivedAdjunction_unit_fac, Category.assoc,
    ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- The first vertex comparison is natural for original complex morphisms. -/
@[reassoc]
theorem moduleLocalizationFirstVertexIso_naturality
    {K L : CochainComplex.Plus (ModuleSheaf X Λ)} (a : K ⟶ L) :
    DerivedCategory.Plus.Q.map ((moduleLowerShriek j Λ).mapCochainComplexPlus.map
        ((moduleInverseImage j Λ).mapCochainComplexPlus.map a)) ≫
      (moduleLocalizationFirstVertexIso j Λ L).hom =
    (moduleLocalizationFirstVertexIso j Λ K).hom ≫
      (moduleDerivedLowerShriek j Λ).map
        ((moduleDerivedInverseImage Λ j).map (DerivedCategory.Plus.Q.map a)) := by
  change _ ≫ ((moduleLowerShriek j Λ).rightDerivedFunctorPlusExactComparison.inv.app _ ≫
      (moduleDerivedLowerShriek j Λ).map
        ((moduleInverseImage j Λ).rightDerivedFunctorPlusUnit.app L)) =
    ((moduleLowerShriek j Λ).rightDerivedFunctorPlusExactComparison.inv.app _ ≫
      (moduleDerivedLowerShriek j Λ).map
        ((moduleInverseImage j Λ).rightDerivedFunctorPlusUnit.app K)) ≫ _
  rw [← Category.assoc]
  erw [(moduleLowerShriek j Λ).rightDerivedFunctorPlusExactComparison.inv.naturality
    ((moduleInverseImage j Λ).mapCochainComplexPlus.map a)]
  simp only [CategoryTheory.Functor.comp_map]
  erw [Category.assoc, ← CategoryTheory.Functor.map_comp]
  erw [(moduleInverseImage j Λ).rightDerivedFunctorPlusUnit.naturality a]
  simp only [CategoryTheory.Functor.comp_map]
  erw [CategoryTheory.Functor.map_comp, Category.assoc]

/-- The closed vertex comparison is natural for original complex morphisms. -/
@[reassoc]
theorem moduleLocalizationThirdVertexIso_naturality
    {K L : CochainComplex.Plus (ModuleSheaf X Λ)} (a : K ⟶ L) :
    DerivedCategory.Plus.Q.map ((moduleDirectImage i Λ).mapCochainComplexPlus.map
        ((moduleInverseImage i Λ).mapCochainComplexPlus.map a)) ≫
      (moduleLocalizationThirdVertexIso Λ i L).hom =
    (moduleLocalizationThirdVertexIso Λ i K).hom ≫
      (moduleDerivedDirectImage Λ i).map
        ((moduleDerivedInverseImage Λ i).map (DerivedCategory.Plus.Q.map a)) := by
  change _ ≫ ((moduleDirectImage i Λ).rightDerivedFunctorPlusUnit.app _ ≫
      (moduleDerivedDirectImage Λ i).map
        ((moduleInverseImage i Λ).rightDerivedFunctorPlusExactComparison.inv.app L)) =
    ((moduleDirectImage i Λ).rightDerivedFunctorPlusUnit.app _ ≫
      (moduleDerivedDirectImage Λ i).map
        ((moduleInverseImage i Λ).rightDerivedFunctorPlusExactComparison.inv.app K)) ≫ _
  rw [← Category.assoc]
  erw [(moduleDirectImage i Λ).rightDerivedFunctorPlusUnit.naturality
    ((moduleInverseImage i Λ).mapCochainComplexPlus.map a)]
  simp only [CategoryTheory.Functor.comp_map]
  erw [Category.assoc, ← CategoryTheory.Functor.map_comp]
  erw [(moduleInverseImage i Λ).rightDerivedFunctorPlusExactComparison.inv.naturality a]
  simp only [CategoryTheory.Functor.comp_map]
  erw [CategoryTheory.Functor.map_comp, Category.assoc]

variable (hcomp : Set.range j = (Set.range i)ᶜ)

/-- Localization with the genuine derived composite vertices and original derived arrows. -/
def moduleLocalizationDerivedTriangle (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    Triangle (DerivedCategory.Plus (ModuleSheaf X Λ)) :=
  Triangle.mk
    ((moduleDerivedLowerShriekAdjunction j Λ).counit.app (DerivedCategory.Plus.Q.obj K))
    ((moduleDerivedAdjunction Λ i).unit.app (DerivedCategory.Plus.Q.obj K))
    ((moduleLocalizationThirdVertexIso Λ i K).inv ≫
      (moduleLocalizationComplexTriangle j Λ i hcomp K).mor₃ ≫
      (shiftFunctor _ (1 : ℤ)).map (moduleLocalizationFirstVertexIso j Λ K).hom)

/-- The original short-exact-complex triangle maps to the actual derived localization triangle. -/
def moduleLocalizationDerivedTriangleIso (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    moduleLocalizationComplexTriangle j Λ i hcomp K ≅
      moduleLocalizationDerivedTriangle j Λ i hcomp K := by
  refine Triangle.isoMk _ _ (moduleLocalizationFirstVertexIso j Λ K)
    (Iso.refl _) (moduleLocalizationThirdVertexIso Λ i K) ?_ ?_ ?_
  · simpa only [moduleLocalizationComplexTriangle, DerivedCategory.Plus.triangleOfSESPlus,
      moduleLocalizationComplex, moduleLocalizationDerivedTriangle, Triangle.mk_mor₁,
      Iso.refl_hom, Category.comp_id] using
      (moduleLocalizationFirstVertexIso_counit j Λ K).symm
  · simpa only [moduleLocalizationComplexTriangle, DerivedCategory.Plus.triangleOfSESPlus,
      moduleLocalizationComplex, moduleLocalizationDerivedTriangle, Triangle.mk_mor₂,
      Iso.refl_hom, Category.id_comp] using moduleLocalizationThirdVertexIso_unit Λ i K
  · dsimp only [moduleLocalizationDerivedTriangle, Triangle.mk_mor₃]
    simp only [← Category.assoc]
    erw [(moduleLocalizationThirdVertexIso Λ i K).hom_inv_id]
    erw [Category.id_comp]
    rfl

/-- The triangle with the original derived counit and unit is distinguished. -/
theorem moduleLocalizationDerivedTriangle_distinguished
    (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    moduleLocalizationDerivedTriangle j Λ i hcomp K ∈
      distTriang (DerivedCategory.Plus (ModuleSheaf X Λ)) :=
  isomorphic_distinguished _ (moduleLocalizationComplexTriangle_distinguished j Λ i hcomp K)
    _ (moduleLocalizationDerivedTriangleIso j Λ i hcomp K).symm

/-- Original complex morphisms induce the transported derived localization diagram. -/
def moduleLocalizationDerivedTriangleMap {K L : CochainComplex.Plus (ModuleSheaf X Λ)}
    (a : K ⟶ L) :
    moduleLocalizationDerivedTriangle j Λ i hcomp K ⟶
      moduleLocalizationDerivedTriangle j Λ i hcomp L :=
  (moduleLocalizationDerivedTriangleIso j Λ i hcomp K).inv ≫
    moduleLocalizationComplexTriangleMap j Λ i hcomp a ≫
      (moduleLocalizationDerivedTriangleIso j Λ i hcomp L).hom

/-- The first transported component is the actual derived composite applied to the map. -/
@[simp]
theorem moduleLocalizationDerivedTriangleMap_hom₁
    {K L : CochainComplex.Plus (ModuleSheaf X Λ)} (a : K ⟶ L) :
    (moduleLocalizationDerivedTriangleMap j Λ i hcomp a).hom₁ =
      (moduleDerivedLowerShriek j Λ).map
        ((moduleDerivedInverseImage Λ j).map (DerivedCategory.Plus.Q.map a)) := by
  change (moduleLocalizationFirstVertexIso j Λ K).inv ≫
    (moduleLocalizationComplexTriangleMap j Λ i hcomp a).hom₁ ≫
      (moduleLocalizationFirstVertexIso j Λ L).hom = _
  rw [show (moduleLocalizationComplexTriangleMap j Λ i hcomp a).hom₁ =
    DerivedCategory.Plus.Q.map ((moduleLowerShriek j Λ).mapCochainComplexPlus.map
      ((moduleInverseImage j Λ).mapCochainComplexPlus.map a)) from
    DerivedCategory.Plus.triangleOfSESPlusMap_hom₁ _ _ _]
  erw [moduleLocalizationFirstVertexIso_naturality, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- The middle transported component is the original localization of the complex map. -/
@[simp]
theorem moduleLocalizationDerivedTriangleMap_hom₂
    {K L : CochainComplex.Plus (ModuleSheaf X Λ)} (a : K ⟶ L) :
    (moduleLocalizationDerivedTriangleMap j Λ i hcomp a).hom₂ =
      DerivedCategory.Plus.Q.map a := by
  change 𝟙 _ ≫ (moduleLocalizationComplexTriangleMap j Λ i hcomp a).hom₂ ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]
  exact DerivedCategory.Plus.triangleOfSESPlusMap_hom₂ _ _ _

/-- The third transported component is the actual closed derived composite on the map. -/
@[simp]
theorem moduleLocalizationDerivedTriangleMap_hom₃
    {K L : CochainComplex.Plus (ModuleSheaf X Λ)} (a : K ⟶ L) :
    (moduleLocalizationDerivedTriangleMap j Λ i hcomp a).hom₃ =
      (moduleDerivedDirectImage Λ i).map
        ((moduleDerivedInverseImage Λ i).map (DerivedCategory.Plus.Q.map a)) := by
  change (moduleLocalizationThirdVertexIso Λ i K).inv ≫
    (moduleLocalizationComplexTriangleMap j Λ i hcomp a).hom₃ ≫
      (moduleLocalizationThirdVertexIso Λ i L).hom = _
  rw [show (moduleLocalizationComplexTriangleMap j Λ i hcomp a).hom₃ =
    DerivedCategory.Plus.Q.map ((moduleDirectImage i Λ).mapCochainComplexPlus.map
      ((moduleInverseImage i Λ).mapCochainComplexPlus.map a)) from
    DerivedCategory.Plus.triangleOfSESPlusMap_hom₃ _ _ _]
  erw [moduleLocalizationThirdVertexIso_naturality, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

end AlgebraicGeometry.Scheme.EtaleCohomology
