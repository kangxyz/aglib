/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.ModuleSingleExchange
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HigherImageIso

/-! # Original module higher images from original derived exchange

The installed single/homology comparisons turn the actual derived
exchange component into an isomorphism between the original ringed higher
images. All four module-derived universes remain independent. No underlying
additive constructibility or replacement coefficient category is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients


universe u wX wS wX' wS'

attribute [local instance] hasSheafifyLarge

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
    [HasDerivedCategory.{wS'} (ModuleSheaf S' Λ)]
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)

/-- The original ringed higher-image comparison when the actual derived exchange
is invertible, obtained
from the original derived exchange and its installed homology comparisons. -/
def moduleHigherBaseChangeIsoOfDerived (q : ℕ) (F : ModuleSheaf X Λ)
    [IsIso (moduleDerivedBaseChangeSingleComponent Λ f f' g g' sq F)] :
    (moduleInverseImage g Λ).obj (((moduleDirectImage f Λ).rightDerived q).obj F) ≅
      ((moduleDirectImage f' Λ).rightDerived q).obj ((moduleInverseImage g' Λ).obj F) := by
  let β := moduleDerivedBaseChangeSingleComponent Λ f f' g g' sq F
  exact Functor.higherImageIsoOfDerived (moduleDirectImage f Λ) (moduleInverseImage g Λ)
    (moduleInverseImage g' Λ) (moduleDirectImage f' Λ) q F (asIso β)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
