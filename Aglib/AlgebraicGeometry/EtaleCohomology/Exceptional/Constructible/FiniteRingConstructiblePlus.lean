/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.FiniteRingDerived
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.CohomologyProperty

/-! # The actual constructible-homology D+ exceptional functor over a finite ring

The full subcategories retain the native derived objects and all their arrows.
The functor is the original exceptional direct image with proved source and
target property lifts. This is a D+ result, with no unproved upper bound.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wM wS wAM wAS

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {X S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wM} (ModuleSheaf (moduleExceptionalCompactification f).Xbar Λ)]
    [HasDerivedCategory.{wAM}
      (AbelianSheaf.{u, u + 1} (moduleExceptionalCompactification f).Xbar)]
    [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]

/-- The original exceptional functor restricted to the actual constructible D+
full subcategories. Both range proofs have been constructed from finite-ring
finiteness; neither a source torsion lift nor a target finiteness premise is assumed. -/
def moduleFiniteRingExceptionalConstructiblePlus :
    (moduleConstructibleCohomologyPlus X Λ).FullSubcategory ⥤
      (moduleConstructibleCohomologyPlus S Λ).FullSubcategory :=
  ObjectProperty.lift (moduleConstructibleCohomologyPlus S Λ)
    ((moduleConstructibleCohomologyPlus X Λ).ι ⋙ moduleFiniteRingTorsionFunctor X Λ ⋙
      moduleExceptionalDirectImagePlus f Λ)
    (fun K n => moduleExceptionalHomology_finiteRing_isConstructible f Λ K.obj K.property n)

/-- Forgetting the output property recovers the original functor and original maps. -/
def moduleFiniteRingExceptionalConstructiblePlusForgetIso :
    moduleFiniteRingExceptionalConstructiblePlus f Λ ⋙
        (moduleConstructibleCohomologyPlus S Λ).ι ≅
      (moduleConstructibleCohomologyPlus X Λ).ι ⋙ moduleFiniteRingTorsionFunctor X Λ ⋙
        moduleExceptionalDirectImagePlus f Λ :=
  Iso.refl _

end AlgebraicGeometry.Scheme.EtaleCohomology
