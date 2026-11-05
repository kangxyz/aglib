/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.AnnihilatorSingle
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Normalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Composition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ClosedExactness
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology

/-! # Finite precomposition on original annihilated coefficients

Only the finite arrow is normalized to its exact native direct image. The outer
arrow need not be proper. The comparison is the original exceptional compositor,
proper normalization, and exact-single comparison, with their unchanged maps.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wY wX wS wG wF wGF

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {Y X : Scheme.{u}} (g : Y ⟶ X) (Λ : Type (u + 1)) [Ring Λ]

/-- The native direct image restricted to original annihilated coefficients.
The underlying object and every underlying arrow are unchanged. -/
def moduleAnnihilatedDirectImage (n : ℕ) :
    (moduleAnnihilated Y Λ n).FullSubcategory ⥤
      (moduleAnnihilated X Λ n).FullSubcategory :=
  ObjectProperty.lift (moduleAnnihilated X Λ n)
    ((moduleAnnihilated Y Λ n).ι ⋙ moduleDirectImage g Λ) (by
      intro M
      let F := moduleDirectImage g Λ
      change n • 𝟙 (F.obj M.obj) = 0
      exact (F.map_nsmul.trans (congrArg (fun a => n • a) (F.map_id M.obj))).symm.trans
        ((congrArg F.map M.property).trans (F.map_zero M.obj M.obj)))

variable [IsFinite g] [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [gModels : ∀ C : Hom.DenseCompactification g,
      HasDerivedCategory.{wG} (ModuleSheaf C.Xbar Λ)]

/-- Original finite exceptional image on annihilated singles agrees with the
single of the original exact finite direct image. This is a whole natural
isomorphism in the original torsion range, not an objectwise replacement. -/
def moduleExceptionalFiniteSingleIso (n : ℕ) (hn : 0 < n) :
    moduleAnnihilatedSingleFunctor Y Λ n hn ⋙
        moduleExceptionalDirectImagePlusTorsion g Λ ≅
      moduleAnnihilatedDirectImage g Λ n ⋙ moduleAnnihilatedSingleFunctor X Λ n hn := by
  apply Functor.fullyFaithfulCancelRight (moduleTorsionCohomologyPlus X Λ).ι
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (moduleExceptionalDirectImagePlusTorsionForgetIso g Λ) ≪≫
    Functor.isoWhiskerLeft _ (moduleExceptionalProperNormalizationIso g Λ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleAnnihilated Y Λ n).ι
      ((moduleDirectImage g Λ).rightDerivedFunctorPlusSingleIso 0) ≪≫
    (Functor.associator _ _ _).symm

variable {S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] [LocallyOfFiniteType f]
    [CompactSpace S] [QuasiSeparatedSpace S]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [fModels : ∀ C : Hom.DenseCompactification f,
      HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]
    [gfModels : ∀ C : Hom.DenseCompactification (g ≫ f),
      HasDerivedCategory.{wGF} (ModuleSheaf C.Xbar Λ)]

/-- Finite precomposition for a possibly nonproper outer arrow, on original
annihilated coefficient objects and maps. The proper normalization is used only
for the finite arrow; the outer functor remains the genuine compactified Rf!. -/
def moduleExceptionalFinitePrecompSingleIso (n : ℕ) (hn : 0 < n) :
    moduleAnnihilatedSingleFunctor Y Λ n hn ⋙
        moduleExceptionalDirectImagePlusTorsion (g ≫ f) Λ ≅
      moduleAnnihilatedDirectImage g Λ n ⋙ moduleAnnihilatedSingleFunctor X Λ n hn ⋙
        moduleExceptionalDirectImagePlusTorsion f Λ :=
  Functor.isoWhiskerLeft _ (moduleExceptionalCompositionIso g f Λ).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleExceptionalFiniteSingleIso g Λ n hn) _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry.Scheme.EtaleCohomology
