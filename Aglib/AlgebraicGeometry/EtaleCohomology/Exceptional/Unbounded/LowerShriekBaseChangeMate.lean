/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.LowerShriekBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenBaseChange
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactInverseMate

/-! # The localized original lower-shriek square retains its exact adjunction mate -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wV wU wY wX
variable {V U Y X : Scheme.{u}} (g : V ⟶ U) (i : V ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X)
  [Etale i] [Etale j] (h : IsPullback g i j f) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wV} (ModuleSheaf V Λ)]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- The inverse original lower-shriek square has the original exact inverse-image mate. -/
theorem moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso_inv_mate :
    (mateEquiv (moduleUnboundedDerivedLowerShriekAdjunction j Λ)
      (moduleUnboundedDerivedLowerShriekAdjunction i Λ)
      (TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ).inv)).natTrans =
      (moduleUnboundedDerivedInverseImageSquareIso Λ f g j i h.w).hom :=
  mapDerivedCategorySquareIso_inverse_mate
    (moduleLowerShriekAdjunction j Λ) (moduleLowerShriekAdjunction i Λ)
    (moduleLowerShriekCartesianBaseChangeIso g i j f h Λ)
    (moduleInverseImageSquareIso Λ f g j i h.w)
    (moduleLowerShriekCartesianBaseChangeIso_inv_mate g i j f h Λ)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso g i j f h Λ)
    (moduleUnboundedDerivedInverseImageSquareIso Λ f g j i h.w) rfl rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
