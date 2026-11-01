/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.Localization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.Composition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperNormalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenNormalization
public import Aglib.CategoryTheory.Triangulated.VertexTransport

/-! # Localization with the original composite exceptional endpoints

All arrows are transported from the original mapped localization triangle by
its specified vertex isomorphisms. The endpoints use the accepted canonical
binary compositor and proper/open normalization on the full native unbounded
category for a torsion coefficient ring.
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

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The closed vertex is normalized by the same proper isomorphism and canonical compositor. -/
def moduleExceptionalUnboundedLocalizationClosedIso
    (K : DerivedCategory (ModuleSheaf X Λ)) :
    (moduleExceptionalDirectImageUnbounded f Λ).obj
        ((moduleUnboundedDerivedDirectImage Λ i).obj
          ((moduleUnboundedDerivedInverseImage Λ i).obj K)) ≅
      (moduleExceptionalDirectImageUnbounded (i ≫ f) Λ).obj
        ((moduleUnboundedDerivedInverseImage Λ i).obj K) :=
  (moduleExceptionalDirectImageUnbounded f Λ).mapIso
    ((moduleExceptionalUnboundedProperNormalizationIso i Λ N hN hΛ).app
      ((moduleUnboundedDerivedInverseImage Λ i).obj K)).symm ≪≫
    (moduleExceptionalDirectImageUnboundedCompIso i f Λ N hN hΛ).app
      ((moduleUnboundedDerivedInverseImage Λ i).obj K)

variable (rawOpenModel : HasDerivedCategory.{wR} (ModuleSheaf X Λ))

/-- The open vertex uses the original raw-open densification normalization
and canonical compositor. -/
def moduleExceptionalUnboundedLocalizationOpenIso :
    letI := hX
    ∀ K : DerivedCategory (ModuleSheaf X Λ),
      (moduleExceptionalDirectImageUnbounded f Λ).obj
          ((moduleUnboundedDerivedLowerShriek j Λ).obj
            ((moduleUnboundedDerivedInverseImage Λ j).obj K)) ≅
        (moduleExceptionalDirectImageUnbounded (j ≫ f) Λ).obj
          ((moduleUnboundedDerivedInverseImage Λ j).obj K) := by
  letI := hX
  intro K
  exact (moduleExceptionalDirectImageUnbounded f Λ).mapIso
    ((moduleExceptionalUnboundedOpenNormalizationIso j Λ rawOpenModel N hN hΛ).app
      ((moduleUnboundedDerivedInverseImage Λ j).obj K)).symm ≪≫
    (moduleExceptionalDirectImageUnboundedCompIso j f Λ N hN hΛ).app
      ((moduleUnboundedDerivedInverseImage Λ j).obj K)

variable (hcomp : Set.range j = (Set.range i)ᶜ)

/-- The actual exceptional localization triangle, with composite exceptional vertices. -/
def moduleExceptionalUnboundedLocalizationTriangle :
    letI := hX
    DerivedCategory (ModuleSheaf X Λ) →
      Triangle (DerivedCategory (ModuleSheaf S Λ)) := by
  letI := hX
  intro K
  exact Triangle.transportVertices
    (moduleExceptionalUnboundedLocalizationRawTriangle f Λ j i hcomp K)
    (moduleExceptionalUnboundedLocalizationOpenIso f j Λ N hN hΛ rawOpenModel K)
    (Iso.refl ((moduleExceptionalDirectImageUnbounded f Λ).obj K))
    (moduleExceptionalUnboundedLocalizationClosedIso f i Λ N hN hΛ K)

/-- The normalization retains a genuine isomorphism of triangles, including its connecting arrow. -/
def moduleExceptionalUnboundedLocalizationTriangleIso :
    letI := hX
    ∀ K : DerivedCategory (ModuleSheaf X Λ),
      moduleExceptionalUnboundedLocalizationRawTriangle f Λ j i hcomp K ≅
        moduleExceptionalUnboundedLocalizationTriangle f j i Λ N hN hΛ rawOpenModel hcomp K := by
  letI := hX
  intro K
  exact Triangle.transportVerticesIso _ _ _ _

/-- The normalized triangle is distinguished in the native ambient derived category. -/
theorem moduleExceptionalUnboundedLocalizationTriangle_distinguished :
    letI := hX
    ∀ K : DerivedCategory (ModuleSheaf X Λ),
      moduleExceptionalUnboundedLocalizationTriangle f j i Λ N hN hΛ rawOpenModel hcomp K ∈
        distTriang (DerivedCategory (ModuleSheaf S Λ)) := by
  let := hX
  intro K
  exact Triangle.transportVertices_distinguished _ _ _ _
    (moduleExceptionalUnboundedLocalizationRawTriangle_distinguished f Λ j i hcomp K)

end AlgebraicGeometry.Scheme.EtaleCohomology
