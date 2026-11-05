/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.TorsionRange
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Layers
public import Aglib.CategoryTheory.Sites.Torsion.AnnihilatorCriterion

/-! # Original internally torsion singles

Only the original coefficient's internal torsion is needed to lift its
actual degree-zero single into the native torsion-cohomology range.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits DerivedCategory.Plus
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u w
attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- The actual single of an internally torsion module has internally torsion
homology, without a specified or uniform annihilator. -/
theorem moduleTorsionSingle_of_isTorsion
    (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
    [HasDerivedCategory.{w} (ModuleSheaf X Λ)]
    (M : ModuleSheaf X Λ) (hM : moduleIsTorsion X Λ M) :
    moduleTorsionCohomologyPlus X Λ
      ((singleFunctor (ModuleSheaf X Λ) 0).obj M) := by
  intro n
  change moduleIsTorsion X Λ ((homologyFunctor (ModuleSheaf X Λ) n).obj
    ((singleFunctor (ModuleSheaf X Λ) 0).obj M))
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have hz := (SheafOfModules.toSheaf (constantRing X Λ)).map_isZero
      (isZero_homology_of_isGE ((singleFunctor (ModuleSheaf X Λ) 0).obj M) 0 n hn)
    exact Sheaf.isTorsion_of_nsmul_id_eq_zero _ 1 (by decide) (hz.eq_of_src _ _)
  · exact moduleIsTorsion_of_iso X Λ
      ((singleFunctorCompHomologyFunctorIso (C := ModuleSheaf X Λ) 0).app M) hM
  · have hz := (SheafOfModules.toSheaf (constantRing X Λ)).map_isZero
      (isZero_homology_of_isLE ((singleFunctor (ModuleSheaf X Λ) 0).obj M) 0 n hn)
    exact Sheaf.isTorsion_of_nsmul_id_eq_zero _ 1 (by decide) (hz.eq_of_src _ _)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
