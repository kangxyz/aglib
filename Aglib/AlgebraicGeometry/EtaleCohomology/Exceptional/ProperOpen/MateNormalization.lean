/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.Comparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.CartesianExchangeComparison
public import Aglib.CategoryTheory.Adjunction.MixedMateRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.Mate

/-! # The proper/open comparison is the original mixed mate

The comparison constructed from restriction and support is identified with
the unit--Cartesian exchange--counit formula. The proof uses conjugacy of the
original maps, not merely invertibility of comparisons between their objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wV wU wX wY

variable (Λ : Type (u + 1)) [Ring Λ]
  {V U X Y : Scheme.{u}} (p : X ⟶ Y)
  (p' : V ⟶ U) (j : U ⟶ Y) (j' : V ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback j' p' p j)
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]

/-- The canonical comparison is the original global mixed mate restricted to
its torsion source, with only the original functor associator inserted. -/
theorem moduleProperOpenComparison_eq_mixedMate :
    moduleProperOpenComparison Λ p p' j j' sq =
      (Functor.associator (moduleTorsionCohomologyPlus V Λ).ι
        (moduleDerivedDirectImage Λ p') (moduleDerivedLowerShriek j Λ)).hom ≫
      Functor.whiskerLeft (moduleTorsionCohomologyPlus V Λ).ι
        (moduleProperOpenMate Λ j j' p' p sq.flip) := by
  exact @Adjunction.restrictionComparison_eq_mate
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (moduleDerivedLowerShriekAdjunction j Λ)
    (moduleDerivedLowerShriekAdjunction j' Λ)
    (moduleDerivedAdjunction Λ p) (moduleDerivedAdjunction Λ p')
    (moduleDerivedLowerShriekCartesianBaseChangeIso p' j' j p sq.flip Λ).hom
    (moduleDerivedCartesianExchangeIso p' j' j p sq.flip Λ)
    (conjugateEquiv_moduleDerivedLowerShriekCartesianBaseChangeIso_hom p' j' j p sq.flip Λ)
    (moduleTorsionCohomologyPlus V Λ).ι inferInstance
    (moduleDerivedBaseChangeMap Λ p p' j j' sq.w.symm)
    (moduleDerivedCartesianExchangeIso_hom p' j' j p sq.flip Λ)
    (moduleProperOpenRestriction Λ p p' j j' sq)
    (moduleProperOpenRestriction_isIso Λ p p' j j' sq) rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
