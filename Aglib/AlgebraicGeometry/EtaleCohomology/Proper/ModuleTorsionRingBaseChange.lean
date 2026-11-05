/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.ProperBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.ModuleTorsionRing

/-! # Original module higher images from original proper derived exchange

The installed single/homology comparisons turn the actual proper derived
exchange component into an isomorphism between the original ringed higher
images. All four module-derived universes remain independent. No underlying
additive constructibility or replacement coefficient category is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

open Coefficients

universe u wX wS wX' wS'

attribute [local instance] hasSheafifyLarge

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
    [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]
    (f : X ⟶ S) [IsProper f] (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)

/-- Over a ring killed by a positive integer, original proper module-derived
exchange is invertible on every original bounded-below coefficient. -/
theorem properModuleDerivedBaseChange_isIso_of_nsmul_one_eq_zero
    (n : ℕ) (hn : 0 < n) (hΛ : n • (1 : Λ) = 0)
    (K : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    IsIso ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K) :=
  properModuleDerivedBaseChange_isIso_of_torsion_homology Λ f f' g g' sq K
    (moduleTorsionCohomologyPlus_of_nsmul_one_eq_zero X Λ n hn hΛ K)

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
