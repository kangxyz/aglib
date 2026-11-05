/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.FiniteComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.CompactificationHigherImage

/-! # Finite comparison between actual compactified higher images

The comparison is restricted to coefficients with a positive annihilator, not to
finite underlying groups or finite coefficient rings. All arrows are the original
single/homology, compactification-comparison, proper-normalization, and exceptional
composition arrows. Source, target, and all middle derived universes are independent.
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

variable {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] [LocallyOfFiniteType f]
    [CompactSpace S] [QuasiSeparatedSpace S]
    (Λ : Type (u + 1)) [Ring Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [fModels : ∀ C : Hom.DenseCompactification f,
      HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]

/-- Whole comparison of the original compactified higher image on annihilated
coefficients with homology of the actual chosen torsion-valued exceptional image. -/
def moduleAnnihilatedCompactificationHomologyIso
    (C : Hom.DenseCompactification f) (n : ℕ) (hn : 0 < n) (q : ℕ) :
    (moduleAnnihilated X Λ n).ι ⋙
        moduleCompactificationHigherDirectImage C.toCompactification Λ q ≅
      moduleAnnihilatedSingleFunctor X Λ n hn ⋙
        moduleExceptionalDirectImagePlusTorsion f Λ ⋙
          (moduleTorsionCohomologyPlus S Λ).ι ⋙
            DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) (q : ℤ) := by
  let H := DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) (q : ℤ)
  let A := moduleAnnihilatedSingleFunctor X Λ n hn
  let e₁ : (moduleAnnihilated X Λ n).ι ⋙
      moduleCompactificationHigherDirectImage C.toCompactification Λ q ≅
        A ⋙ moduleCompactificationFunctor f Λ C ⋙ H :=
    Functor.isoWhiskerLeft (moduleAnnihilated X Λ n).ι
      (moduleCompactificationHigherDirectImageHomologyIso C.toCompactification Λ q)
  exact e₁ ≪≫
    Functor.isoWhiskerLeft A
      (Functor.isoWhiskerRight (moduleExceptionalDirectImagePlusIso f Λ C).symm H) ≪≫
    Functor.isoWhiskerLeft A
      (Functor.isoWhiskerRight (moduleExceptionalDirectImagePlusTorsionForgetIso f Λ).symm H)

variable {Y : Scheme.{u}} (g : Y ⟶ X) [IsFinite g]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
    [gModels : ∀ C : Hom.DenseCompactification g,
      HasDerivedCategory.{wG} (ModuleSheaf C.Xbar Λ)]
    [gfModels : ∀ C : Hom.DenseCompactification (g ≫ f),
      HasDerivedCategory.{wGF} (ModuleSheaf C.Xbar Λ)]

/-- Original finite precomposition for two supplied genuine compactifications.
The finite source arrow is proper; the outer morphism is not required proper. -/
def moduleAnnihilatedFiniteCompactificationIso
    (C : Hom.DenseCompactification f) (D : Hom.DenseCompactification (g ≫ f))
    (n : ℕ) (hn : 0 < n) (q : ℕ) :
    (moduleAnnihilated Y Λ n).ι ⋙
        moduleCompactificationHigherDirectImage D.toCompactification Λ q ≅
      moduleAnnihilatedDirectImage g Λ n ⋙ (moduleAnnihilated X Λ n).ι ⋙
        moduleCompactificationHigherDirectImage C.toCompactification Λ q := by
  let H := (moduleTorsionCohomologyPlus S Λ).ι ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) (q : ℤ)
  exact moduleAnnihilatedCompactificationHomologyIso (g ≫ f) Λ D n hn q ≪≫
    Functor.isoWhiskerRight (moduleExceptionalFinitePrecompSingleIso g Λ f n hn) H ≪≫
    Functor.isoWhiskerLeft (moduleAnnihilatedDirectImage g Λ n)
      (moduleAnnihilatedCompactificationHomologyIso f Λ C n hn q).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
