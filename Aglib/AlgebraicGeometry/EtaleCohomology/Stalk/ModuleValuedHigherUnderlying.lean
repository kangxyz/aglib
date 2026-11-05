/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ConstantModulePresheaf
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ModuleCoefficientCoproducts
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.RightDerived

public import Aglib.CategoryTheory.Functor.ComparisonAction

/-! # Original native and valued higher images over arbitrary rings

This lower leaf retains the exact native coefficient-equivalence and original
higher-image underlying comparisons. It makes no scalar-linearity assertion
about the module category. The scalar-compatible lift is a separate consumer.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u wMX wMS wAX wAS

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

open Coefficients

variable {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type (u + 1)) [Ring Λ]

/-- Use the existing native enough-injectives supplier at its generic constant-ring head. -/
local instance constantRingModuleSheaf_enoughInjectives (T : Scheme.{u}) :
    EnoughInjectives
      (ModuleCat.Sheaf.ConstantRing.ModuleSheaf.{u + 1, u, u + 1, u + 1}
        T.smallEtaleTopology Λ) :=
  Coefficients.moduleSheaf_enoughInjectives T Λ

local instance valuedSheaf_enoughInjectives (T : Scheme.{u}) :
    EnoughInjectives (ModuleValuedSheaf T Λ) :=
  EnoughInjectives.of_equivalence (moduleSheafEquivalence T Λ).functor

local instance valuedDirectImage_additive : (moduleValuedDirectImage f Λ).Additive where
  map_add := by intros; apply ObjectProperty.hom_ext; ext U x; rfl

/-- Original higher direct image, conjugated only by the original coefficient equivalence. -/
def moduleHigherDirectImageValuedComparison (q : ℕ) :
    (moduleSheafEquivalence X Λ).functor ⋙
        ((moduleDirectImage f Λ).rightDerived q ⋙ (moduleSheafEquivalence S Λ).inverse) ≅
      (moduleValuedDirectImage f Λ).rightDerived q :=
  Functor.isoWhiskerLeft (moduleSheafEquivalence X Λ).functor
      (ModuleCat.Sheaf.ConstantRing.moduleDirectImageRightDerivedComparison
        (siteBaseChange f) S.smallEtaleTopology X.smallEtaleTopology Λ q) ≪≫
    (Functor.associator (moduleSheafEquivalence X Λ).functor
      (moduleSheafEquivalence X Λ).inverse
      ((moduleValuedDirectImage f Λ).rightDerived q)).symm ≪≫
    Functor.isoWhiskerRight (moduleSheafEquivalence X Λ).unitIso.symm
      ((moduleValuedDirectImage f Λ).rightDerived q) ≪≫
    Functor.leftUnitor ((moduleValuedDirectImage f Λ).rightDerived q)

/-- Return the same valued higher image to the original native ringed modules. -/
def moduleHigherDirectImageNativeComparison (q : ℕ) :
    (moduleValuedDirectImage f Λ).rightDerived q ⋙ (moduleSheafEquivalence S Λ).functor ≅
      (moduleSheafEquivalence X Λ).functor ⋙ (moduleDirectImage f Λ).rightDerived q :=
  Functor.isoWhiskerRight (moduleHigherDirectImageValuedComparison f Λ q).symm
      (moduleSheafEquivalence S Λ).functor ≪≫
    Functor.associator (moduleSheafEquivalence X Λ).functor
      ((moduleDirectImage f Λ).rightDerived q ⋙ (moduleSheafEquivalence S Λ).inverse)
      (moduleSheafEquivalence S Λ).functor ≪≫
    Functor.isoWhiskerLeft (moduleSheafEquivalence X Λ).functor
      (Functor.associator ((moduleDirectImage f Λ).rightDerived q)
        (moduleSheafEquivalence S Λ).inverse (moduleSheafEquivalence S Λ).functor) ≪≫
    Functor.isoWhiskerLeft (moduleSheafEquivalence X Λ).functor
      (Functor.isoWhiskerLeft ((moduleDirectImage f Λ).rightDerived q)
        (moduleSheafEquivalence S Λ).counitIso) ≪≫
    Functor.isoWhiskerLeft (moduleSheafEquivalence X Λ).functor
      (Functor.rightUnitor ((moduleDirectImage f Λ).rightDerived q))

variable [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]

/-- Forgetting the actual valued higher image gives the original abelian higher image. -/
def moduleValuedHigherDirectImageUnderlyingIso (q : ℕ) :
    (moduleValuedDirectImage f Λ).rightDerived q ⋙
        ModuleCat.Sheaf.underlying Λ S.smallEtaleTopology ≅
      ModuleCat.Sheaf.underlying Λ X.smallEtaleTopology ⋙ higherDirectImage f q :=
  Functor.isoWhiskerRight (moduleHigherDirectImageValuedComparison f Λ q).symm
      (ModuleCat.Sheaf.underlying Λ S.smallEtaleTopology) ≪≫
    Functor.associator (moduleSheafEquivalence X Λ).functor
      ((moduleDirectImage f Λ).rightDerived q ⋙ (moduleSheafEquivalence S Λ).inverse)
      (ModuleCat.Sheaf.underlying Λ S.smallEtaleTopology) ≪≫
    Functor.isoWhiskerLeft (moduleSheafEquivalence X Λ).functor
      (Functor.associator ((moduleDirectImage f Λ).rightDerived q)
        (moduleSheafEquivalence S Λ).inverse
        (ModuleCat.Sheaf.underlying Λ S.smallEtaleTopology)) ≪≫
    Functor.isoWhiskerLeft (moduleSheafEquivalence X Λ).functor
      (Functor.isoWhiskerLeft ((moduleDirectImage f Λ).rightDerived q)
        (moduleSheafInverseUnderlyingIso S Λ)) ≪≫
    Functor.isoWhiskerLeft (moduleSheafEquivalence X Λ).functor
      (moduleHigherDirectImageUnderlyingIso.{u, wMX, wMS, wAX, wAS} Λ f q) ≪≫
    (Functor.associator (moduleSheafEquivalence X Λ).functor
      (SheafOfModules.toSheaf (constantRing X Λ)) (higherDirectImage f q)).symm ≪≫
    Functor.isoWhiskerRight (moduleSheafUnderlyingIso X Λ) (higherDirectImage f q)

/-- Actual higher direct images of original constant module sheaves. -/
abbrev constantModuleValuedHigherDirectImage (q : ℕ) :
    ModuleCat.{u + 1} Λ ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    (moduleValuedDirectImage f Λ).rightDerived q

/-- The actual constant-module target has the original abelian target underneath. -/
def constantModuleValuedHigherDirectImageUnderlyingIso (q : ℕ) :
    constantModuleValuedHigherDirectImage f Λ q ⋙
        ModuleCat.Sheaf.underlying Λ S.smallEtaleTopology ≅
      constantModuleUnderlying (X := X) Λ ⋙ higherDirectImage f q :=
  Functor.whiskeredComparison
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    ((moduleValuedDirectImage f Λ).rightDerived q)
    (ModuleCat.Sheaf.underlying Λ S.smallEtaleTopology)
    (ModuleCat.Sheaf.underlying Λ X.smallEtaleTopology) (higherDirectImage f q)
    (constantModuleUnderlying (X := X) Λ)
    (moduleValuedHigherDirectImageUnderlyingIso.{u, wMX, wMS, wAX, wAS} f Λ q)
    (ModuleCat.Sheaf.constantUnderlyingIso Λ X.smallEtaleTopology)

end AlgebraicGeometry.Scheme.EtaleCohomology
