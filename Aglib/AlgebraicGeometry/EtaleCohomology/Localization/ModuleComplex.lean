/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ModuleShortExact
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Open
public import Aglib.Algebra.Homology.DerivedCategory.Plus.ShortExact

/-!
# The original module localization sequence on bounded-below complexes

The original counit and unit act degreewise. The genuine module-sheaf
localization theorem proves the resulting sequence short exact, hence gives
the native distinguished short-exact-complex triangle in D+. Identification
with the separately derived composite functors is a subsequent comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u w

variable {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (Λ : Type (u + 1)) [Ring Λ] (i : Z ⟶ X) [IsClosedImmersion i]
  (hcomp : Set.range j = (Set.range i)ᶜ)

/-- The original module counit and unit form the actual sequence of complexes. -/
def moduleLocalizationComplex (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    ShortComplex (CochainComplex.Plus (ModuleSheaf X Λ)) :=
  ShortComplex.mk
    ((moduleLowerShriekAdjunction j Λ).mapCochainComplexPlus.counit.app K)
    ((moduleInverseImageAdjunction i Λ).mapCochainComplexPlus.unit.app K) (by
      apply ObjectProperty.hom_ext
      ext n : 1
      exact moduleLocalization_counit_comp_unit j Λ i hcomp (K.obj.X n))

/-- Short exactness is proved degreewise with the original module localization theorem. -/
theorem moduleLocalizationComplex_shortExact (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    ((moduleLocalizationComplex j Λ i hcomp K).map
      (CochainComplex.Plus.ι (ModuleSheaf X Λ))).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  change (moduleLocalizationShortComplex j Λ i hcomp (K.obj.X n)).ShortExact
  exact moduleLocalization_shortExact j Λ i hcomp (K.obj.X n)

/-- A complex morphism induces the original localization diagram. -/
def moduleLocalizationComplexMap {K L : CochainComplex.Plus (ModuleSheaf X Λ)}
    (a : K ⟶ L) :
    moduleLocalizationComplex j Λ i hcomp K ⟶ moduleLocalizationComplex j Λ i hcomp L where
  τ₁ := (moduleLowerShriek j Λ).mapCochainComplexPlus.map
    ((moduleInverseImage j Λ).mapCochainComplexPlus.map a)
  τ₂ := a
  τ₃ := (moduleDirectImage i Λ).mapCochainComplexPlus.map
    ((moduleInverseImage i Λ).mapCochainComplexPlus.map a)
  comm₁₂ := (moduleLowerShriekAdjunction j Λ).mapCochainComplexPlus.counit.naturality a
  comm₂₃ := (moduleInverseImageAdjunction i Λ).mapCochainComplexPlus.unit.naturality a

variable [HasDerivedCategory.{w} (ModuleSheaf X Λ)]

/-- The native D+ triangle with original localization arrows and cone connecting map. -/
def moduleLocalizationComplexTriangle (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    Triangle (DerivedCategory.Plus (ModuleSheaf X Λ)) :=
  DerivedCategory.Plus.triangleOfSESPlus (moduleLocalizationComplex_shortExact j Λ i hcomp K)

/-- The actual short-exact-complex localization triangle is distinguished. -/
theorem moduleLocalizationComplexTriangle_distinguished
    (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    moduleLocalizationComplexTriangle j Λ i hcomp K ∈
      distTriang (DerivedCategory.Plus (ModuleSheaf X Λ)) :=
  DerivedCategory.Plus.triangleOfSESPlus_distinguished
    (moduleLocalizationComplex_shortExact j Λ i hcomp K)

/-- Original complex maps give the native connecting-map naturality square. -/
def moduleLocalizationComplexTriangleMap {K L : CochainComplex.Plus (ModuleSheaf X Λ)}
    (a : K ⟶ L) :
    moduleLocalizationComplexTriangle j Λ i hcomp K ⟶
      moduleLocalizationComplexTriangle j Λ i hcomp L :=
  DerivedCategory.Plus.triangleOfSESPlusMap
    (moduleLocalizationComplex_shortExact j Λ i hcomp K)
    (moduleLocalizationComplex_shortExact j Λ i hcomp L)
    (moduleLocalizationComplexMap j Λ i hcomp a)

/-- The original triangle-map component is the localized original complex map. -/
@[simp]
theorem moduleLocalizationComplexTriangleMap_hom₁
    {K L : CochainComplex.Plus (ModuleSheaf X Λ)} (a : K ⟶ L) :
    (moduleLocalizationComplexTriangleMap j Λ i hcomp a).hom₁ =
      DerivedCategory.Plus.Q.map ((moduleLowerShriek j Λ).mapCochainComplexPlus.map
      ((moduleInverseImage j Λ).mapCochainComplexPlus.map a)) :=
  DerivedCategory.Plus.triangleOfSESPlusMap_hom₁
    (moduleLocalizationComplex_shortExact j Λ i hcomp K)
    (moduleLocalizationComplex_shortExact j Λ i hcomp L)
    (moduleLocalizationComplexMap j Λ i hcomp a)

/-- The original triangle-map component is the localized original complex map. -/
@[simp]
theorem moduleLocalizationComplexTriangleMap_hom₂
    {K L : CochainComplex.Plus (ModuleSheaf X Λ)} (a : K ⟶ L) :
    (moduleLocalizationComplexTriangleMap j Λ i hcomp a).hom₂ =
      DerivedCategory.Plus.Q.map (a) :=
  DerivedCategory.Plus.triangleOfSESPlusMap_hom₂
    (moduleLocalizationComplex_shortExact j Λ i hcomp K)
    (moduleLocalizationComplex_shortExact j Λ i hcomp L)
    (moduleLocalizationComplexMap j Λ i hcomp a)

/-- The original triangle-map component is the localized original complex map. -/
@[simp]
theorem moduleLocalizationComplexTriangleMap_hom₃
    {K L : CochainComplex.Plus (ModuleSheaf X Λ)} (a : K ⟶ L) :
    (moduleLocalizationComplexTriangleMap j Λ i hcomp a).hom₃ =
      DerivedCategory.Plus.Q.map ((moduleDirectImage i Λ).mapCochainComplexPlus.map
      ((moduleInverseImage i Λ).mapCochainComplexPlus.map a)) :=
  DerivedCategory.Plus.triangleOfSESPlusMap_hom₃
    (moduleLocalizationComplex_shortExact j Λ i hcomp K)
    (moduleLocalizationComplex_shortExact j Λ i hcomp L)
    (moduleLocalizationComplexMap j Λ i hcomp a)

-- The native short-exact triangle hides its vertex carriers behind full-subcategory definitions.
-- Keep transparency local to the functor laws at that original comparison boundary.
set_option backward.isDefEq.respectTransparency false in
/-- The original distinguished localization triangles form an actual functor. -/
def moduleLocalizationComplexTriangleFunctor :
    CochainComplex.Plus (ModuleSheaf X Λ) ⥤
      Triangle (DerivedCategory.Plus (ModuleSheaf X Λ)) where
  obj := moduleLocalizationComplexTriangle j Λ i hcomp
  map a := moduleLocalizationComplexTriangleMap j Λ i hcomp a
  map_id K := by
    apply Triangle.hom_ext
    · change (moduleLocalizationComplexTriangleMap j Λ i hcomp (𝟙 K)).hom₁ =
        𝟙 (DerivedCategory.Plus.Q.obj ((moduleLowerShriek j Λ).mapCochainComplexPlus.obj
        ((moduleInverseImage j Λ).mapCochainComplexPlus.obj K)))
      rw [moduleLocalizationComplexTriangleMap_hom₁]
      exact ((moduleInverseImage j Λ).mapCochainComplexPlus ⋙
        (moduleLowerShriek j Λ).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).map_id K
    · change (moduleLocalizationComplexTriangleMap j Λ i hcomp (𝟙 K)).hom₂ =
        𝟙 (DerivedCategory.Plus.Q.obj (K))
      rw [moduleLocalizationComplexTriangleMap_hom₂]
      exact DerivedCategory.Plus.Q.map_id K
    · change (moduleLocalizationComplexTriangleMap j Λ i hcomp (𝟙 K)).hom₃ =
        𝟙 (DerivedCategory.Plus.Q.obj ((moduleDirectImage i Λ).mapCochainComplexPlus.obj
        ((moduleInverseImage i Λ).mapCochainComplexPlus.obj K)))
      rw [moduleLocalizationComplexTriangleMap_hom₃]
      exact ((moduleInverseImage i Λ).mapCochainComplexPlus ⋙
        (moduleDirectImage i Λ).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).map_id K
  map_comp a b := by
    apply Triangle.hom_ext
    · change (moduleLocalizationComplexTriangleMap j Λ i hcomp (a ≫ b)).hom₁ =
        (moduleLocalizationComplexTriangleMap j Λ i hcomp a).hom₁ ≫
          (moduleLocalizationComplexTriangleMap j Λ i hcomp b).hom₁
      rw [moduleLocalizationComplexTriangleMap_hom₁,
        moduleLocalizationComplexTriangleMap_hom₁, moduleLocalizationComplexTriangleMap_hom₁]
      simp only [Functor.map_comp]
    · change (moduleLocalizationComplexTriangleMap j Λ i hcomp (a ≫ b)).hom₂ =
        (moduleLocalizationComplexTriangleMap j Λ i hcomp a).hom₂ ≫
          (moduleLocalizationComplexTriangleMap j Λ i hcomp b).hom₂
      rw [moduleLocalizationComplexTriangleMap_hom₂,
        moduleLocalizationComplexTriangleMap_hom₂, moduleLocalizationComplexTriangleMap_hom₂]
      simp only [Functor.map_comp]
    · change (moduleLocalizationComplexTriangleMap j Λ i hcomp (a ≫ b)).hom₃ =
        (moduleLocalizationComplexTriangleMap j Λ i hcomp a).hom₃ ≫
          (moduleLocalizationComplexTriangleMap j Λ i hcomp b).hom₃
      rw [moduleLocalizationComplexTriangleMap_hom₃,
        moduleLocalizationComplexTriangleMap_hom₃, moduleLocalizationComplexTriangleMap_hom₃]
      simp only [Functor.map_comp]

end AlgebraicGeometry.Scheme.EtaleCohomology
