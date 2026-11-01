/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ScalarRestrictionExact
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleAdjunctionCompatibility

/-! # Original inverse and direct images under restriction of coefficient scalars -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

attribute [local instance] hasSheafifyModules moduleRestrictScalars_preservesSheafification

variable {X S : Scheme.{u}} (f : S ⟶ X)
  {Λ Γ : Type (u + 1)} [CommRing Λ] [CommRing Γ] (φ : Λ →+* Γ)

/-- Ordinary module-valued direct image commutes literally with scalar restriction. -/
def moduleValuedDirectImageScalarRestrictionIso :
    moduleValuedDirectImage f Γ ⋙ moduleValuedRestrictScalars X φ ≅
      moduleValuedRestrictScalars S φ ⋙ moduleValuedDirectImage f Λ := Iso.refl _

/-- The original continuous-site inverse image and actual scalar restriction commute. -/
def moduleValuedInverseImageScalarRestrictionIso :
    moduleValuedInverseImage f Γ ⋙ moduleValuedRestrictScalars S φ ≅
      moduleValuedRestrictScalars X φ ⋙ moduleValuedInverseImage f Λ := by
  letI : (ModuleCat.restrictScalars.{u + 1} φ).PreservesLeftKanExtensions
      (siteBaseChange f).op := by
    intro P
    infer_instance
  exact (Functor.sheafPullbackCoefficientIso (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
    (ModuleCat.restrictScalars.{u + 1} φ)).symm

/-- The left coefficient-change composite retains the original inverse equivalence. -/
def moduleDirectImageScalarRestrictionLeftIso :
    (moduleDirectImage f Γ ⋙ moduleRestrictScalars X φ) ⋙
        (moduleSheafEquivalence X Λ).inverse ≅
      (moduleSheafEquivalence S Γ).inverse ⋙
        moduleValuedDirectImage f Γ ⋙ moduleValuedRestrictScalars X φ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (moduleRestrictScalarsComparison X φ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleDirectImageComparison f Γ) _ ≪≫
    Functor.associator _ _ _

/-- The right coefficient-change composite uses the same original inverse equivalence. -/
def moduleDirectImageScalarRestrictionRightIso :
    (moduleRestrictScalars S φ ⋙ moduleDirectImage f Λ) ⋙
        (moduleSheafEquivalence X Λ).inverse ≅
      (moduleSheafEquivalence S Γ).inverse ⋙
        moduleValuedRestrictScalars S φ ⋙ moduleValuedDirectImage f Λ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (moduleDirectImageComparison f Λ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleRestrictScalarsComparison S φ) _ ≪≫
    Functor.associator _ _ _

/-- The original native direct image commutes with actual ring restriction. -/
def moduleDirectImageScalarRestrictionIso :
    moduleDirectImage f Γ ⋙ moduleRestrictScalars X φ ≅
      moduleRestrictScalars S φ ⋙ moduleDirectImage f Λ :=
  ((Functor.whiskeringRight (ModuleSheaf S Γ) (ModuleSheaf X Λ)
    (ModuleValuedSheaf X Λ)).obj (moduleSheafEquivalence X Λ).inverse).preimageIso
      (moduleDirectImageScalarRestrictionLeftIso f φ ≪≫
        Functor.isoWhiskerLeft _ (moduleValuedDirectImageScalarRestrictionIso f φ) ≪≫
        (moduleDirectImageScalarRestrictionRightIso f φ).symm)

/-- The left coefficient-change composite retains the original inverse equivalence. -/
def moduleInverseImageScalarRestrictionLeftIso :
    (moduleInverseImage f Γ ⋙ moduleRestrictScalars S φ) ⋙
        (moduleSheafEquivalence S Λ).inverse ≅
      (moduleSheafEquivalence X Γ).inverse ⋙
        moduleValuedInverseImage f Γ ⋙ moduleValuedRestrictScalars S φ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (moduleRestrictScalarsComparison S φ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleInverseImageValuedIso Γ f) _ ≪≫
    Functor.associator _ _ _

/-- The right coefficient-change composite uses the same original inverse equivalence. -/
def moduleInverseImageScalarRestrictionRightIso :
    (moduleRestrictScalars X φ ⋙ moduleInverseImage f Λ) ⋙
        (moduleSheafEquivalence S Λ).inverse ≅
      (moduleSheafEquivalence X Γ).inverse ⋙
        moduleValuedRestrictScalars X φ ⋙ moduleValuedInverseImage f Λ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (moduleInverseImageValuedIso Λ f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleRestrictScalarsComparison X φ) _ ≪≫
    Functor.associator _ _ _

/-- The original native inverse image commutes with actual ring restriction. -/
def moduleInverseImageScalarRestrictionIso :
    moduleInverseImage f Γ ⋙ moduleRestrictScalars S φ ≅
      moduleRestrictScalars X φ ⋙ moduleInverseImage f Λ :=
  ((Functor.whiskeringRight (ModuleSheaf X Γ) (ModuleSheaf S Λ)
    (ModuleValuedSheaf S Λ)).obj (moduleSheafEquivalence S Λ).inverse).preimageIso
      (moduleInverseImageScalarRestrictionLeftIso f φ ≪≫
        Functor.isoWhiskerLeft _ (moduleValuedInverseImageScalarRestrictionIso f φ) ≪≫
        (moduleInverseImageScalarRestrictionRightIso f φ).symm)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
