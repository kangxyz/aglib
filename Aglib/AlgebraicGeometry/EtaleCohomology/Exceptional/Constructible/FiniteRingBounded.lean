/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.FiniteRingConstructiblePlus
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompactificationAmplitude
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Constructible.CohomologyProperty

/-! # The original finite-ring exceptional image on bounded constructible objects

The bounded range is an intrinsic full subcategory of the already selected
native D+. Actual geometric amplitude supplies the output bound; established
finite-ring constructibility supplies every output homology property. No new
derived model, compactification, or coefficient replacement is introduced.
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

/-- The actual exceptional image preserves the intrinsic bounded constructible
range. Both the upper bound and all homology constructibility are proved. -/
theorem moduleExceptional_finiteRing_boundedConstructible
    (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (hK : moduleBoundedConstructibleCohomologyPlus X Λ K) :
    moduleBoundedConstructibleCohomologyPlus S Λ
      ((moduleExceptionalDirectImagePlus f Λ).obj
        ((moduleFiniteRingTorsionFunctor X Λ).obj K)) := by
  refine ⟨moduleExceptionalHomology_finiteRing_isConstructible f Λ K hK.1, ?_⟩
  obtain ⟨a, b, ha, hb⟩ := hK.2
  let : K.IsGE a := ha
  let : K.IsLE b := hb
  let C := (moduleExceptionalCompactification f).toCompactification
  obtain ⟨d, hd⟩ := exists_moduleCompactification_upperAmplitude C Λ
    (Nat.card Λ) Nat.card_pos card_nsmul_eq_zero'
  refine ⟨a, (d : ℤ) + b, ?_, hd K a b ha hb⟩
  let : ((moduleDerivedLowerShriek C.j Λ).obj K).IsGE a :=
    (moduleLowerShriek C.j Λ).rightDerivedFunctorPlus_isGE K a
  change ((moduleDerivedDirectImage Λ C.p).obj
    ((moduleDerivedLowerShriek C.j Λ).obj K)).IsGE a
  exact (moduleDirectImage C.p Λ).rightDerivedFunctorPlus_isGE _ a

/-- The original exceptional functor on the actual bounded constructible
full subcategories, retaining its original coefficient maps. -/
def moduleFiniteRingExceptionalBoundedConstructible :
    (moduleBoundedConstructibleCohomologyPlus X Λ).FullSubcategory ⥤
      (moduleBoundedConstructibleCohomologyPlus S Λ).FullSubcategory :=
  ObjectProperty.lift (moduleBoundedConstructibleCohomologyPlus S Λ)
    ((moduleBoundedConstructibleCohomologyPlus X Λ).ι ⋙
      moduleFiniteRingTorsionFunctor X Λ ⋙ moduleExceptionalDirectImagePlus f Λ)
    (fun K => moduleExceptional_finiteRing_boundedConstructible f Λ K.obj K.property)

/-- Forgetting bounded constructibility recovers the unchanged original functor. -/
def moduleFiniteRingExceptionalBoundedConstructibleForgetIso :
    moduleFiniteRingExceptionalBoundedConstructible f Λ ⋙
        (moduleBoundedConstructibleCohomologyPlus S Λ).ι ≅
      (moduleBoundedConstructibleCohomologyPlus X Λ).ι ⋙
        moduleFiniteRingTorsionFunctor X Λ ⋙ moduleExceptionalDirectImagePlus f Λ :=
  Iso.refl _

end AlgebraicGeometry.Scheme.EtaleCohomology
