/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ExactInputHomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.TorsionRange
public import Mathlib.Algebra.CharP.Lemmas

/-! # Original compactified higher images and the actual exceptional functor

The coefficient functor is literally lower shriek followed by the native
higher proper image. Its whole comparison with compactified derived homology
uses exact input, not a false assertion that lower shriek preserves injectives.
Over a positive-characteristic ring, the original native single functor lands
in the existing torsion range without changing any module coefficient.
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

variable {X S : Scheme.{u}} {f : X ⟶ S} (C : Hom.Compactification f)
    (Λ : Type (u + 1)) [Ring Λ]

/-- Actual compactified higher image of native coefficients, with no derived
realization needed to specify its original coefficient maps. -/
abbrev moduleCompactificationHigherDirectImage (q : ℕ) : ModuleSheaf X Λ ⥤ ModuleSheaf S Λ :=
  moduleLowerShriek C.j Λ ⋙ (moduleDirectImage C.p Λ).rightDerived q

variable [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- The original exact-single and proper single/homology maps compare the
whole compactified coefficient functor with its original derived realization. -/
def moduleCompactificationHigherDirectImageHomologyIso (q : ℕ) :
    moduleCompactificationHigherDirectImage C Λ q ≅
      DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0 ⋙
        moduleDerivedLowerShriek C.j Λ ⋙ moduleDerivedDirectImage Λ C.p ⋙
          DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) (q : ℤ) :=
  Functor.exactInputRightDerivedHomologyIso (moduleLowerShriek C.j Λ)
    (moduleDirectImage C.p Λ) q

/-- The original single functor, restricted only in its codomain to the actual
torsion-cohomology range supplied by a positive annihilator of the scalar unit. -/
def moduleTorsionSingleFunctor (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0) :
    ModuleSheaf X Λ ⥤ (moduleTorsionCohomologyPlus X Λ).FullSubcategory :=
  ObjectProperty.lift (moduleTorsionCohomologyPlus X Λ)
    (DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0)
    (fun M => moduleTorsionCohomology_of_nsmul_one_eq_zero X Λ N hN hΛ
      ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X Λ) 0).obj M).obj)

/-- The same whole comparison now lands in the existing raw compactification
functor. The source lift changes no object or morphism under inclusion. -/
def moduleCompactificationHigherDirectImageTorsionHomologyIso
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0) (q : ℕ) :
    moduleCompactificationHigherDirectImage C Λ q ≅
      moduleTorsionSingleFunctor Λ N hN hΛ ⋙ moduleRawCompactificationFunctor C Λ ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) (q : ℤ) :=
  moduleCompactificationHigherDirectImageHomologyIso C Λ q

end AlgebraicGeometry.Scheme.EtaleCohomology
