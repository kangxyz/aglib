/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ModuleShortExact
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnboundedOpen
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# The original module localization sequence on unbounded complexes

The original module lower-shriek counit and closed inverse-image unit act on
arbitrary integer cochain complexes. Their degreewise short exact sequence
gives the native unbounded short-exact-complex triangle, retaining its actual
mapping-cone connecting map. Original complex morphisms give natural triangle
maps. No boundedness or proper-base-change premise is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u w

variable {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (Λ : Type (u + 1)) [Ring Λ] (i : Z ⟶ X) [IsClosedImmersion i]
  (hcomp : Set.range j = (Set.range i)ᶜ)

/-- The original counit and unit form the actual unbounded sequence of complexes. -/
def moduleUnboundedLocalizationComplex (K : CochainComplex (ModuleSheaf X Λ) ℤ) :
    ShortComplex (CochainComplex (ModuleSheaf X Λ) ℤ) :=
  ShortComplex.mk
    (((moduleLowerShriekAdjunction j Λ).mapHomologicalComplex (.up ℤ)).counit.app K)
    (((moduleInverseImageAdjunction i Λ).mapHomologicalComplex (.up ℤ)).unit.app K) (by
      ext n : 1
      exact moduleLocalization_counit_comp_unit j Λ i hcomp (K.X n))

/-- The actual localization theorem proves short exactness in every integer degree. -/
theorem moduleUnboundedLocalizationComplex_shortExact
    (K : CochainComplex (ModuleSheaf X Λ) ℤ) :
    (moduleUnboundedLocalizationComplex j Λ i hcomp K).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  change (moduleLocalizationShortComplex j Λ i hcomp (K.X n)).ShortExact
  exact moduleLocalization_shortExact j Λ i hcomp (K.X n)

/-- Original complex maps induce the original localization diagram. -/
def moduleUnboundedLocalizationComplexMap {K L : CochainComplex (ModuleSheaf X Λ) ℤ}
    (a : K ⟶ L) :
    moduleUnboundedLocalizationComplex j Λ i hcomp K ⟶
      moduleUnboundedLocalizationComplex j Λ i hcomp L where
  τ₁ := ((moduleLowerShriek j Λ).mapHomologicalComplex (.up ℤ)).map
    (((moduleInverseImage j Λ).mapHomologicalComplex (.up ℤ)).map a)
  τ₂ := a
  τ₃ := ((moduleDirectImage i Λ).mapHomologicalComplex (.up ℤ)).map
    (((moduleInverseImage i Λ).mapHomologicalComplex (.up ℤ)).map a)
  comm₁₂ := ((moduleLowerShriekAdjunction j Λ).mapHomologicalComplex (.up ℤ)).counit.naturality a
  comm₂₃ := ((moduleInverseImageAdjunction i Λ).mapHomologicalComplex (.up ℤ)).unit.naturality a

variable [HasDerivedCategory.{w} (ModuleSheaf X Λ)]

/-- The native unbounded localization triangle with its original connecting map. -/
def moduleUnboundedLocalizationComplexTriangle (K : CochainComplex (ModuleSheaf X Λ) ℤ) :
    Triangle (DerivedCategory (ModuleSheaf X Λ)) :=
  DerivedCategory.triangleOfSES (moduleUnboundedLocalizationComplex_shortExact j Λ i hcomp K)

/-- The original short-exact-complex triangle is distinguished without boundedness. -/
theorem moduleUnboundedLocalizationComplexTriangle_distinguished
    (K : CochainComplex (ModuleSheaf X Λ) ℤ) :
    moduleUnboundedLocalizationComplexTriangle j Λ i hcomp K ∈
      distTriang (DerivedCategory (ModuleSheaf X Λ)) :=
  DerivedCategory.triangleOfSES_distinguished
    (moduleUnboundedLocalizationComplex_shortExact j Λ i hcomp K)

/-- The native triangle map retains the original connecting-map naturality square. -/
def moduleUnboundedLocalizationComplexTriangleMap
    {K L : CochainComplex (ModuleSheaf X Λ) ℤ} (a : K ⟶ L) :
    moduleUnboundedLocalizationComplexTriangle j Λ i hcomp K ⟶
      moduleUnboundedLocalizationComplexTriangle j Λ i hcomp L :=
  DerivedCategory.triangleOfSES.map
    (moduleUnboundedLocalizationComplex_shortExact j Λ i hcomp K)
    (moduleUnboundedLocalizationComplex_shortExact j Λ i hcomp L)
    (moduleUnboundedLocalizationComplexMap j Λ i hcomp a)

/-- The first triangle component is the localized original open-composite map. -/
@[simp]
theorem moduleUnboundedLocalizationComplexTriangleMap_hom₁
    {K L : CochainComplex (ModuleSheaf X Λ) ℤ} (a : K ⟶ L) :
    (moduleUnboundedLocalizationComplexTriangleMap j Λ i hcomp a).hom₁ =
      DerivedCategory.Q.map (((moduleLowerShriek j Λ).mapHomologicalComplex (.up ℤ)).map
        (((moduleInverseImage j Λ).mapHomologicalComplex (.up ℤ)).map a)) := rfl

/-- The middle triangle component is the original localized complex map. -/
@[simp]
theorem moduleUnboundedLocalizationComplexTriangleMap_hom₂
    {K L : CochainComplex (ModuleSheaf X Λ) ℤ} (a : K ⟶ L) :
    (moduleUnboundedLocalizationComplexTriangleMap j Λ i hcomp a).hom₂ =
      DerivedCategory.Q.map a := rfl

/-- The last triangle component is the localized original closed-composite map. -/
@[simp]
theorem moduleUnboundedLocalizationComplexTriangleMap_hom₃
    {K L : CochainComplex (ModuleSheaf X Λ) ℤ} (a : K ⟶ L) :
    (moduleUnboundedLocalizationComplexTriangleMap j Λ i hcomp a).hom₃ =
      DerivedCategory.Q.map (((moduleDirectImage i Λ).mapHomologicalComplex (.up ℤ)).map
        (((moduleInverseImage i Λ).mapHomologicalComplex (.up ℤ)).map a)) := rfl

-- The native short-exact triangle exposes its vertex carriers only after reduction.
set_option backward.isDefEq.respectTransparency false in
/-- The original unbounded short-exact localization triangles form a functor. -/
def moduleUnboundedLocalizationComplexTriangleFunctor :
    CochainComplex (ModuleSheaf X Λ) ℤ ⥤ Triangle (DerivedCategory (ModuleSheaf X Λ)) where
  obj := moduleUnboundedLocalizationComplexTriangle j Λ i hcomp
  map a := moduleUnboundedLocalizationComplexTriangleMap j Λ i hcomp a
  map_id K := by
    apply Triangle.hom_ext
    · change DerivedCategory.Q.map
        (((moduleLowerShriek j Λ).mapHomologicalComplex (.up ℤ)).map
          (((moduleInverseImage j Λ).mapHomologicalComplex (.up ℤ)).map (𝟙 K))) = 𝟙 _
      exact (((moduleInverseImage j Λ).mapHomologicalComplex (.up ℤ)) ⋙
        ((moduleLowerShriek j Λ).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q).map_id K
    · change DerivedCategory.Q.map (𝟙 K) = 𝟙 _
      exact DerivedCategory.Q.map_id K
    · change DerivedCategory.Q.map
        (((moduleDirectImage i Λ).mapHomologicalComplex (.up ℤ)).map
          (((moduleInverseImage i Λ).mapHomologicalComplex (.up ℤ)).map (𝟙 K))) = 𝟙 _
      exact (((moduleInverseImage i Λ).mapHomologicalComplex (.up ℤ)) ⋙
        ((moduleDirectImage i Λ).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q).map_id K
  map_comp a b := by
    apply Triangle.hom_ext
    · exact (((moduleInverseImage j Λ).mapHomologicalComplex (.up ℤ)) ⋙
        ((moduleLowerShriek j Λ).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q).map_comp a b
    · exact DerivedCategory.Q.map_comp a b
    · exact (((moduleInverseImage i Λ).mapHomologicalComplex (.up ℤ)) ⋙
        ((moduleDirectImage i Λ).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q).map_comp a b

end AlgebraicGeometry.Scheme.EtaleCohomology
