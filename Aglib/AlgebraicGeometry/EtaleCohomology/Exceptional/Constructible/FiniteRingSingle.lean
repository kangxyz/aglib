/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.FiniteRingCompactification
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.DirectImage
public import Mathlib.GroupTheory.OrderOfElement

/-! # Actual exceptional images of constructible finite-ring singles

The finite ring supplies its actual positive additive cardinal annihilator.
The original single functor is therefore lifted into the already existing
native torsion D+ range by a proof, not an assumed factorization. The original
chosen exceptional functor then has constructible homology in every degree.
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

/-- The actual native single functor lifted to internal torsion using the
positive additive order of the finite ring. It has the unchanged single maps. -/
def moduleFiniteRingSingleFunctor (X : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)] :
    ModuleSheaf X Λ ⥤ (moduleTorsionCohomologyPlus X Λ).FullSubcategory :=
  moduleTorsionSingleFunctor Λ (Nat.card Λ) Nat.card_pos card_nsmul_eq_zero'

/-- The original choice-independent Rf! of any constructible finite-ring
coefficient single has constructible homology in every integer degree.
This is a genuine consumer of the original chosen compactification, not a new
exceptional functor and not a postulated bounded constructible-category lift. -/
theorem moduleExceptionalSingleHomology_finiteRing_isConstructible
    {X S : Scheme.{u}} [IsNoetherian S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wM} (ModuleSheaf (moduleExceptionalCompactification f).Xbar Λ)]
    [HasDerivedCategory.{wAM}
      (AbelianSheaf.{u, u + 1} (moduleExceptionalCompactification f).Xbar)]
    [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]
    (M : ModuleSheaf X Λ)
    (hM : Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence X Λ).inverse.obj M)) (i : ℤ) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence S Λ).inverse.obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) i).obj
          ((moduleExceptionalDirectImagePlus f Λ).obj
            ((moduleFiniteRingSingleFunctor X Λ).obj M)))) :=
  moduleCompactificationSingleHomology_finiteRing_isConstructible
    (moduleExceptionalCompactification f).toCompactification Λ i M hM

end AlgebraicGeometry.Scheme.EtaleCohomology
