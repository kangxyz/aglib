/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ScalarRestrictionTriangle
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ScalarRestrictionNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.Derived
public import Aglib.Algebra.Homology.DerivedCategory.Plus.ShortExactMapSquare
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ScalarRestrictionTriangleHom

/-!
# Natural scalar restriction of the original D+ localization triangle

The entire triangle comparison descends through the original localization Q.
Its complex comparison retains the original counit, unit, and connecting arrow.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wXΓ wXΛ wUΓ wUΛ wZΓ wZΛ

variable {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (i : Z ⟶ X) [IsClosedImmersion i]
  {Λ Γ : Type (u + 1)} [CommRing Λ] [CommRing Γ] (φ : Λ →+* Γ)
  (hcomp : Set.range j = (Set.range i)ᶜ)
  [HasDerivedCategory.{wXΓ} (ModuleSheaf X Γ)]
  [HasDerivedCategory.{wXΛ} (ModuleSheaf X Λ)]

/-- The actual complete triangle comparison is natural in complexes. -/
theorem moduleLocalizationComplexTriangleScalarRestrictionIso_naturality
    {K L : CochainComplex.Plus (ModuleSheaf X Γ)} (a : K ⟶ L) :
    (moduleDerivedRestrictScalars X φ).mapTriangle.map
        (moduleLocalizationComplexTriangleMap j Γ i hcomp a) ≫
      (moduleLocalizationComplexTriangleScalarRestrictionIso j i φ hcomp L).hom =
    (moduleLocalizationComplexTriangleScalarRestrictionIso j i φ hcomp K).hom ≫
      moduleLocalizationComplexTriangleMap j Λ i hcomp
        ((moduleRestrictScalars X φ).mapCochainComplexPlus.map a) := by
  rw [moduleLocalizationComplexTriangleScalarRestrictionIso_hom,
    moduleLocalizationComplexTriangleScalarRestrictionIso_hom]
  exact DerivedCategory.Plus.mapTriangleOfSESPlusIso_square (moduleRestrictScalars X φ)
    (moduleLocalizationComplex_shortExact j Γ i hcomp K)
    (moduleLocalizationComplex_shortExact j Γ i hcomp L)
    (moduleLocalizationComplex_shortExact j Λ i hcomp
      ((moduleRestrictScalars X φ).mapCochainComplexPlus.obj K))
    (moduleLocalizationComplex_shortExact j Λ i hcomp
      ((moduleRestrictScalars X φ).mapCochainComplexPlus.obj L))
    (moduleLocalizationComplexScalarRestrictionIso j i φ hcomp K)
    (moduleLocalizationComplexScalarRestrictionIso j i φ hcomp L)
    (moduleLocalizationComplexMap j Γ i hcomp a)
    (moduleLocalizationComplexMap j Λ i hcomp
      ((moduleRestrictScalars X φ).mapCochainComplexPlus.map a))
    (moduleLocalizationComplexScalarRestrictionIso_naturality j i φ hcomp a)

/-- The complete scalar triangle comparison before localization, as a natural isomorphism. -/
def moduleLocalizationComplexTriangleScalarRestrictionNatIso :
    moduleLocalizationComplexTriangleFunctor j Γ i hcomp ⋙
        (moduleDerivedRestrictScalars X φ).mapTriangle ≅
      (moduleRestrictScalars X φ).mapCochainComplexPlus ⋙
        moduleLocalizationComplexTriangleFunctor j Λ i hcomp :=
  NatIso.ofComponents (moduleLocalizationComplexTriangleScalarRestrictionIso j i φ hcomp)
    (by intro K L a
        exact moduleLocalizationComplexTriangleScalarRestrictionIso_naturality j i φ hcomp a)

variable [HasDerivedCategory.{wUΓ} (ModuleSheaf U Γ)]
  [HasDerivedCategory.{wUΛ} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wZΓ} (ModuleSheaf Z Γ)]
  [HasDerivedCategory.{wZΛ} (ModuleSheaf Z Λ)]

/-- The canonical natural scalar comparison for the entire original D+ localization triangle. -/
def moduleLocalizationTriangleScalarRestrictionNatIso :
    moduleLocalizationTriangleFunctor j Γ i hcomp ⋙
        (moduleDerivedRestrictScalars X φ).mapTriangle ≅
      moduleDerivedRestrictScalars X φ ⋙ moduleLocalizationTriangleFunctor j Λ i hcomp := by
  let F := moduleRestrictScalars X φ
  letI : IsIso F.rightDerivedFunctorPlusUnit :=
    F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let A := moduleLocalizationTriangleFunctor j Γ i hcomp ⋙
    (moduleDerivedRestrictScalars X φ).mapTriangle
  let B := moduleDerivedRestrictScalars X φ ⋙ moduleLocalizationTriangleFunctor j Λ i hcomp
  refine Localization.liftNatIso DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (ModuleSheaf X Γ))
      (DerivedCategory.Plus.Q ⋙ A) (DerivedCategory.Plus.Q ⋙ B) A B ?_
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleLocalizationTriangleFunctorFac j Γ i hcomp) _ ≪≫
    moduleLocalizationComplexTriangleScalarRestrictionNatIso j i φ hcomp ≪≫
    Functor.isoWhiskerLeft F.mapCochainComplexPlus
      (moduleLocalizationTriangleFunctorFac j Λ i hcomp).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso F.rightDerivedFunctorPlusUnit) _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry.Scheme.EtaleCohomology
