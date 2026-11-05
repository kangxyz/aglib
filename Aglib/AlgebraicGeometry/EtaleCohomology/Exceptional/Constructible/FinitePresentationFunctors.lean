/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.FinitePresentationBounded

/-! # Original exceptional functors on constructible D+ and Db

A positive annihilator of the coefficient ring supplies internal torsion for
every original input. No source torsion proof or target finiteness premise is
required. The inclusions retain all original objects and arrows.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM
attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- The whole original D+ lands in internal torsion for a Z/N coefficient ring. -/
def modulePositiveCharacteristicTorsionFunctor (X : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    (N : ℕ) (hN : 0 < N) (hΛ : (N : Λ) = 0) :
    DerivedCategory.Plus (ModuleSheaf X Λ) ⥤
      (moduleTorsionCohomologyPlus X Λ).FullSubcategory :=
  ObjectProperty.lift (moduleTorsionCohomologyPlus X Λ) (𝟭 _)
    (fun K => moduleTorsionCohomology_of_nsmul_one_eq_zero X Λ
      N hN ((nsmul_one N).trans hΛ) K.obj)

variable {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    (Λ : Type (u + 1)) [Ring Λ] [IsNoetherianRing Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wM} (ModuleSheaf (moduleExceptionalCompactification f).Xbar Λ)]
    (N : ℕ) (hN : 0 < N) (hΛ : (N : Λ) = 0)

/-- Original exceptional direct image on constructible D+, with torsion produced. -/
def moduleFinitePresentationExceptionalConstructiblePlus :
    (moduleConstructibleCohomologyPlus X Λ).FullSubcategory ⥤
      (moduleConstructibleCohomologyPlus S Λ).FullSubcategory :=
  ObjectProperty.lift (moduleConstructibleCohomologyPlus S Λ)
    ((moduleConstructibleCohomologyPlus X Λ).ι ⋙
      modulePositiveCharacteristicTorsionFunctor X Λ N hN hΛ ⋙
      moduleExceptionalDirectImagePlus f Λ)
    (fun K n => moduleExceptionalHomology_finitePresentation_isConstructible
      f Λ N hN hΛ
      ((modulePositiveCharacteristicTorsionFunctor X Λ N hN hΛ).obj K.obj) K.property n)

/-- Original exceptional direct image on bounded constructible complexes. -/
def moduleFinitePresentationExceptionalBoundedConstructible :
    (moduleBoundedConstructibleCohomologyPlus X Λ).FullSubcategory ⥤
      (moduleBoundedConstructibleCohomologyPlus S Λ).FullSubcategory :=
  ObjectProperty.lift (moduleBoundedConstructibleCohomologyPlus S Λ)
    ((moduleBoundedConstructibleCohomologyPlus X Λ).ι ⋙
      modulePositiveCharacteristicTorsionFunctor X Λ N hN hΛ ⋙
      moduleExceptionalDirectImagePlus f Λ)
    (fun K => (moduleExceptional_finitePresentation_boundedConstructible
      f Λ N hN hΛ
      ((modulePositiveCharacteristicTorsionFunctor X Λ N hN hΛ).obj K.obj) K.property).2)

/-- Forgetting the constructed D+ range proof retains precisely the original maps. -/
def moduleFinitePresentationExceptionalConstructiblePlusForgetIso :
    moduleFinitePresentationExceptionalConstructiblePlus f Λ N hN hΛ ⋙
        (moduleConstructibleCohomologyPlus S Λ).ι ≅
      (moduleConstructibleCohomologyPlus X Λ).ι ⋙
        modulePositiveCharacteristicTorsionFunctor X Λ N hN hΛ ⋙
        moduleExceptionalDirectImagePlus f Λ := Iso.refl _

/-- Forgetting the constructed bounded range proof retains precisely the original maps. -/
def moduleFinitePresentationExceptionalBoundedConstructibleForgetIso :
    moduleFinitePresentationExceptionalBoundedConstructible f Λ N hN hΛ ⋙
        (moduleBoundedConstructibleCohomologyPlus S Λ).ι ≅
      (moduleBoundedConstructibleCohomologyPlus X Λ).ι ⋙
        modulePositiveCharacteristicTorsionFunctor X Λ N hN hΛ ⋙
        moduleExceptionalDirectImagePlus f Λ := Iso.refl _

end AlgebraicGeometry.Scheme.EtaleCohomology
