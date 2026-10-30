/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleAdjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ScalarRestriction
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Coefficients
public import Aglib.CategoryTheory.Topos.Slice.ForwardComparison

/-! # Genuine lower shriek commutes with actual restriction of coefficient rings -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyModules moduleRestrictScalars_preservesSheafification

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
  {Λ Γ : Type (u + 1)} [Ring Λ] [Ring Γ] (φ : Λ →+* Γ)

local instance moduleScalarRestrictionPreservesColimits (ι : Type u) :
    PreservesColimitsOfShape (Discrete ι) (ModuleCat.restrictScalars.{u + 1} φ) where
  preservesColimit {K} := ModuleCat.preservesColimit_restrictScalars φ K

/-- Inverse slice equivalence commutes literally with restriction of coefficient rings. -/
def moduleEtaleSliceInverseScalarRestrictionIso :
    sheafCompose ((Scheme.smallEtaleTopology X).over (Scheme.Etale.mk j))
        (ModuleCat.restrictScalars.{u + 1} φ) ⋙ (moduleEtaleSliceSheafEquivalence j Λ).inverse ≅
      (moduleEtaleSliceSheafEquivalence j Γ).inverse ⋙ moduleValuedRestrictScalars U φ :=
  Iso.refl _

/-- Forward slice equivalence commutes through the original equivalence units and counits. -/
def moduleEtaleSliceScalarRestrictionIso :
    (moduleEtaleSliceSheafEquivalence j Γ).functor ⋙
      sheafCompose ((Scheme.smallEtaleTopology X).over (Scheme.Etale.mk j))
        (ModuleCat.restrictScalars.{u + 1} φ) ≅
      moduleValuedRestrictScalars U φ ⋙ (moduleEtaleSliceSheafEquivalence j Λ).functor :=
  Equivalence.forwardComparison (moduleEtaleSliceSheafEquivalence j Γ)
      (moduleEtaleSliceSheafEquivalence j Λ) _ _
    (moduleEtaleSliceInverseScalarRestrictionIso j φ)

/-- The native forward comparison retains exactly the original unit/counit chain. -/
theorem moduleEtaleSliceScalarRestrictionIso_eq_original :
    moduleEtaleSliceScalarRestrictionIso j φ =
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (moduleEtaleSliceSheafEquivalence j Λ).counitIso.symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (moduleEtaleSliceInverseScalarRestrictionIso j φ) _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleEtaleSliceSheafEquivalence j Γ).unitIso.symm _ ≪≫
    Functor.leftUnitor _ := by
  exact Equivalence.forwardComparison_eq_original (moduleEtaleSliceSheafEquivalence j Γ)
      (moduleEtaleSliceSheafEquivalence j Λ) _ _
    (moduleEtaleSliceInverseScalarRestrictionIso j φ)

/-- Actual module-valued lower shriek commutes with restriction along a ring homomorphism. -/
def moduleValuedLowerShriekScalarRestrictionIso :
    moduleValuedLowerShriek j Γ ⋙ moduleValuedRestrictScalars X φ ≅
      moduleValuedRestrictScalars U φ ⋙ moduleValuedLowerShriek j Λ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Sheaf.SliceCohomology.lowerShriekCoefficientIso
        (ModuleCat.restrictScalars.{u + 1} φ)
        (Scheme.Etale.mk j) (Scheme.smallEtaleTopology X)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleEtaleSliceScalarRestrictionIso j φ) _ ≪≫
    Functor.associator _ _ _

/-- Native lower shriek after the inverse coefficient equivalence. -/
def moduleLowerShriekValuedIso (R : Type (u + 1)) [Ring R] :
    moduleLowerShriek j R ⋙ (moduleSheafEquivalence X R).inverse ≅
      (moduleSheafEquivalence U R).inverse ⋙ moduleValuedLowerShriek j R :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (moduleSheafEquivalence X R).unitIso.symm ≪≫
    Functor.rightUnitor _

/-- The left scalar-change composite retains its actual inverse coefficient equivalence. -/
def moduleLowerShriekScalarRestrictionLeftIso :
    (moduleLowerShriek j Γ ⋙ moduleRestrictScalars X φ) ⋙
        (moduleSheafEquivalence X Λ).inverse ≅
      (moduleSheafEquivalence U Γ).inverse ⋙
        moduleValuedLowerShriek j Γ ⋙ moduleValuedRestrictScalars X φ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (moduleRestrictScalarsComparison X φ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleLowerShriekValuedIso j Γ) _ ≪≫
    Functor.associator _ _ _

/-- The right scalar-change composite retains the same inverse coefficient equivalence. -/
def moduleLowerShriekScalarRestrictionRightIso :
    (moduleRestrictScalars U φ ⋙ moduleLowerShriek j Λ) ⋙
        (moduleSheafEquivalence X Λ).inverse ≅
      (moduleSheafEquivalence U Γ).inverse ⋙
        moduleValuedRestrictScalars U φ ⋙ moduleValuedLowerShriek j Λ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (moduleLowerShriekValuedIso j Λ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleRestrictScalarsComparison U φ) _ ≪≫
    Functor.associator _ _ _

/-- Genuine lower shriek commutes with native restriction along the constant ring sheaf map. -/
def moduleLowerShriekScalarRestrictionIso :
    moduleLowerShriek j Γ ⋙ moduleRestrictScalars X φ ≅
      moduleRestrictScalars U φ ⋙ moduleLowerShriek j Λ :=
  ((Functor.whiskeringRight (ModuleSheaf U Γ) (ModuleSheaf X Λ)
    (ModuleValuedSheaf X Λ)).obj (moduleSheafEquivalence X Λ).inverse).preimageIso
      (moduleLowerShriekScalarRestrictionLeftIso j φ ≪≫
        Functor.isoWhiskerLeft _ (moduleValuedLowerShriekScalarRestrictionIso j φ) ≪≫
        (moduleLowerShriekScalarRestrictionRightIso j φ).symm)

end AlgebraicGeometry.Scheme.EtaleCohomology
