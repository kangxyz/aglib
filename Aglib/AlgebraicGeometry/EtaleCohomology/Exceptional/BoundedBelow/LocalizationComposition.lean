/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Localization

/-! # Localization with the original composite exceptional endpoints

All arrows are transported from the original mapped localization triangle by
its specified vertex isomorphisms. The endpoints use the accepted canonical
binary compositor and proper/open normalization on the native torsion range.
No triangulation of the torsion full subcategory is postulated.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wU wZ wX wS wF wJ wI wJF wIF wR
variable {U Z X S : Scheme.{u}}
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace S] [QuasiSeparatedSpace S]
  (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  (i : Z ⟶ X) [IsClosedImmersion i]
  (Λ : Type (u + 1)) [Ring Λ]
  [hU : HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [fModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]
  [jModels : ∀ C : Hom.DenseCompactification j,
    HasDerivedCategory.{wJ} (ModuleSheaf C.Xbar Λ)]
  [iModels : ∀ C : Hom.DenseCompactification i,
    HasDerivedCategory.{wI} (ModuleSheaf C.Xbar Λ)]
  [jfModels : ∀ C : Hom.DenseCompactification (j ≫ f),
    HasDerivedCategory.{wJF} (ModuleSheaf C.Xbar Λ)]
  [ifModels : ∀ C : Hom.DenseCompactification (i ≫ f),
    HasDerivedCategory.{wIF} (ModuleSheaf C.Xbar Λ)]

/-- The closed vertex is normalized by the same proper isomorphism and canonical compositor. -/
def moduleExceptionalLocalizationClosedIso
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    (moduleExceptionalChosenAmbientFunctor f Λ).obj
        ((moduleDerivedDirectImage Λ i).obj ((moduleDerivedInverseImage Λ i).obj K.obj)) ≅
      (moduleExceptionalDirectImagePlus (i ≫ f) Λ).obj
        ((moduleDerivedInverseImageTorsion i Λ).obj K) :=
  (moduleExceptionalChosenAmbientFunctor f Λ).mapIso
    ((moduleExceptionalProperNormalizationIso i Λ).app
      ((moduleDerivedInverseImageTorsion i Λ).obj K)).symm ≪≫
    (moduleTorsionCohomologyPlus S Λ).ι.mapIso
      ((moduleExceptionalCompositionIso i f Λ).app ((moduleDerivedInverseImageTorsion i Λ).obj K))

variable (rawOpenModel : HasDerivedCategory.{wR} (ModuleSheaf X Λ))

/-- The open vertex uses the original raw-open densification normalization
and canonical compositor. -/
def moduleExceptionalLocalizationOpenIso :
    letI := hX
    ∀ K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory,
      (moduleExceptionalChosenAmbientFunctor f Λ).obj
          ((moduleDerivedLowerShriek j Λ).obj ((moduleDerivedInverseImage Λ j).obj K.obj)) ≅
        (moduleExceptionalDirectImagePlus (j ≫ f) Λ).obj
          ((moduleDerivedInverseImageTorsion j Λ).obj K) := by
  letI := hX
  intro K
  exact (moduleExceptionalChosenAmbientFunctor f Λ).mapIso
    ((moduleExceptionalOpenNormalizationIso j Λ rawOpenModel).app
      ((moduleDerivedInverseImageTorsion j Λ).obj K)).symm ≪≫
    (moduleTorsionCohomologyPlus S Λ).ι.mapIso
      ((moduleExceptionalCompositionIso j f Λ).app ((moduleDerivedInverseImageTorsion j Λ).obj K))

variable (hcomp : Set.range j = (Set.range i)ᶜ)

/-- The actual exceptional localization triangle, with composite exceptional vertices. -/
def moduleExceptionalLocalizationTriangle :
    letI := hX
    (moduleTorsionCohomologyPlus X Λ).FullSubcategory →
      Triangle (DerivedCategory.Plus (ModuleSheaf S Λ)) := by
  letI := hX
  intro K
  exact Triangle.transportVertices (moduleExceptionalLocalizationRawTriangle f Λ j i hcomp K)
    (moduleExceptionalLocalizationOpenIso f j Λ rawOpenModel K)
    (Iso.refl ((moduleExceptionalDirectImagePlus f Λ).obj K))
    (moduleExceptionalLocalizationClosedIso f i Λ K)

/-- The normalization retains a genuine isomorphism of triangles, including its connecting arrow. -/
def moduleExceptionalLocalizationTriangleIso :
    letI := hX
    ∀ K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory,
      moduleExceptionalLocalizationRawTriangle f Λ j i hcomp K ≅
        moduleExceptionalLocalizationTriangle f j i Λ rawOpenModel hcomp K := by
  letI := hX
  intro K
  exact Triangle.transportVerticesIso _ _ _ _

/-- The normalized triangle is distinguished in the native ambient derived category. -/
theorem moduleExceptionalLocalizationTriangle_distinguished :
    letI := hX
    ∀ K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory,
      moduleExceptionalLocalizationTriangle f j i Λ rawOpenModel hcomp K ∈
        distTriang (DerivedCategory.Plus (ModuleSheaf S Λ)) := by
  let := hX
  intro K
  exact Triangle.transportVertices_distinguished _ _ _ _
    (moduleExceptionalLocalizationRawTriangle_distinguished f Λ j i hcomp K)

end AlgebraicGeometry.Scheme.EtaleCohomology
