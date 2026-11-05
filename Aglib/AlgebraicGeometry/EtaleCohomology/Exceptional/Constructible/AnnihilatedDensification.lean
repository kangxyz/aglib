/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.AnnihilatorSingle
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.CompactificationHigherImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.Densification

/-! # Original annihilated higher images under schematic densification

The whole natural comparison is built from the original exact-single
homology comparisons and the original densification map. It does not assume
that the original open immersion is dense, or that the ring or underlying
coefficient is finite. No new exceptional functor is selected.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wC wD

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X S : Scheme.{u}} {f : X ⟶ S}
  (C : Hom.Compactification f) [QuasiCompact C.j]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf (Hom.Compactification.densify C).Xbar Λ)]

/-- Densification identifies the original natural-degree compactified higher
images on the actual positive-annihilator full subcategory, with all original
coefficient maps retained. The two ambient derived worlds are independent. -/
def moduleAnnihilatedCompactificationDensificationIso
    (n : ℕ) (hn : 0 < n) (q : ℕ) :
    (moduleAnnihilated X Λ n).ι ⋙ moduleCompactificationHigherDirectImage C Λ q ≅
      (moduleAnnihilated X Λ n).ι ⋙
        moduleCompactificationHigherDirectImage
          (Hom.Compactification.densify C).toCompactification Λ q := by
  let H := DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) (q : ℤ)
  let A := moduleAnnihilatedSingleFunctor X Λ n hn
  let eC : (moduleAnnihilated X Λ n).ι ⋙ moduleCompactificationHigherDirectImage C Λ q ≅
      A ⋙ moduleRawCompactificationFunctor C Λ ⋙ H :=
    Functor.isoWhiskerLeft (moduleAnnihilated X Λ n).ι
      (moduleCompactificationHigherDirectImageHomologyIso C Λ q)
  let eD : (moduleAnnihilated X Λ n).ι ⋙
        moduleCompactificationHigherDirectImage
          (Hom.Compactification.densify C).toCompactification Λ q ≅
      A ⋙ moduleRawCompactificationFunctor
        (Hom.Compactification.densify C).toCompactification Λ ⋙ H :=
    Functor.isoWhiskerLeft (moduleAnnihilated X Λ n).ι
      (moduleCompactificationHigherDirectImageHomologyIso
        (Hom.Compactification.densify C).toCompactification Λ q)
  exact eC ≪≫ Functor.isoWhiskerLeft A
    (Functor.isoWhiskerRight (moduleCompactificationDensificationIso C Λ) H) ≪≫ eD.symm

end AlgebraicGeometry.Scheme.EtaleCohomology
