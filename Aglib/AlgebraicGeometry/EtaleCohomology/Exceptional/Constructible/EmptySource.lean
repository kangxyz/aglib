/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Localization
public import Aglib.AlgebraicGeometry.Sites.EtaleEmpty

/-! # Original bounded-below module objects on an empty source

Actual abelian coefficients vanish by empty-cover descent. The original
faithful underlying functor and native all-homology criterion transfer this to
any selected native bounded-below derived realization. Every chosen
exceptional image is then zero by its original additive ambient functor.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wM
attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- Every native module coefficient on an empty scheme is zero. -/
theorem moduleSheaf_isZero_of_empty
    (X : Scheme.{u}) [IsEmpty X] (Λ : Type (u + 1)) [Ring Λ]
    (M : ModuleSheaf X Λ) : IsZero M := by
  let U := SheafOfModules.toSheaf (constantRing X Λ)
  apply (IsZero.iff_id_eq_zero M).mpr
  apply U.map_injective
  rw [U.map_id, U.map_zero]
  exact (Scheme.Etale.isZero_of_isEmpty (U.obj M)).eq_of_src _ _

/-- Every original native D+ module object on an empty scheme is zero. -/
theorem moduleDerivedPlus_isZero_of_empty
    (X : Scheme.{u}) [IsEmpty X] (Λ : Type (u + 1)) [Ring Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    (K : DerivedCategory.Plus (ModuleSheaf X Λ)) : IsZero K := by
  let : IsIso (0 : K ⟶ K) := (DerivedCategory.Plus.isIso_iff _).mpr fun n =>
    (moduleSheaf_isZero_of_empty X Λ _).isIso (moduleSheaf_isZero_of_empty X Λ _) _
  exact IsZero.of_epi_eq_zero (0 : K ⟶ K) rfl

/-- The actual exceptional image of any original torsion D+ input on an empty
source is zero. All supplied native derived worlds are retained. -/
theorem moduleExceptional_isZero_of_empty
    {X S : Scheme.{u}} [IsEmpty X] [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Λ : Type (u + 1)) [Ring Λ]
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [∀ C : Hom.DenseCompactification f, HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    IsZero ((moduleExceptionalDirectImagePlus f Λ).obj K) :=
  (moduleExceptionalChosenAmbientFunctor f Λ).map_isZero
    (moduleDerivedPlus_isZero_of_empty X Λ K.obj)

end AlgebraicGeometry.Scheme.EtaleCohomology
