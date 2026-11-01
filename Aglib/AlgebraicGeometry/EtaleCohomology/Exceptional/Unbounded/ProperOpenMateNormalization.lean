/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperOpenComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperOpenMate
public import Aglib.CategoryTheory.Adjunction.MixedMateRestriction

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
its native unbounded source, with only the original functor associator inserted. -/
theorem moduleUnboundedProperOpenComparison_eq_mixedMate :
    moduleUnboundedProperOpenComparison Λ p p' j j' sq =
      (Functor.associator (𝟭 (DerivedCategory (ModuleSheaf V Λ)))
        (moduleUnboundedDerivedDirectImage Λ p') (moduleUnboundedDerivedLowerShriek j Λ)).hom ≫
      Functor.whiskerLeft (𝟭 (DerivedCategory (ModuleSheaf V Λ)))
        (moduleUnboundedProperOpenMate p' j' j p sq.flip Λ) := by
  exact @Adjunction.restrictionComparison_eq_mate
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (moduleUnboundedDerivedLowerShriekAdjunction j Λ)
    (moduleUnboundedDerivedLowerShriekAdjunction j' Λ)
    (moduleUnboundedDerivedAdjunction Λ p) (moduleUnboundedDerivedAdjunction Λ p')
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso p' j' j p sq.flip Λ).hom
    (moduleUnboundedCartesianExchangeIso p' j' j p sq.flip Λ)
    (conjugateEquiv_moduleUnboundedLowerShriekCartesianBaseChangeIso_hom p' j' j p sq.flip Λ)
    (𝟭 (DerivedCategory (ModuleSheaf V Λ))) inferInstance
    (moduleUnboundedDerivedBaseChangeMap Λ p p' j j' sq.w.symm)
    rfl
    (moduleUnboundedProperOpenRestriction Λ p p' j j' sq)
    (moduleUnboundedProperOpenRestriction_isIso Λ p p' j j' sq) rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
