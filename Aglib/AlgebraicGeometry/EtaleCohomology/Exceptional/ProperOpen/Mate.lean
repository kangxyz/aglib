/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenBaseChangeConjugacy
public import Aglib.CategoryTheory.Adjunction.Mates.Whole

/-! # The original global proper/open mixed mate

The literal mate exists on all bounded-below objects. Its comparison with the
proper/torsion isomorphism and its coherence are supplied by later leaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wU₀ wU₁ wX₀ wX₁

variable (Λ : Type (u + 1)) [Ring Λ]

/-- The original mixed mate of the original open Cartesian comparison. This
map exists without properness or a torsion hypothesis; those govern its being
an isomorphism, not its definition. -/
def moduleProperOpenMate {U₀ U₁ X₀ X₁ : Scheme.{u}}
    (j₀ : U₀ ⟶ X₀) (j₁ : U₁ ⟶ X₁) (g : U₁ ⟶ U₀) (f : X₁ ⟶ X₀)
    [Etale j₀] [Etale j₁] (h : IsPullback g j₁ j₀ f)
    [HasDerivedCategory.{wU₀} (ModuleSheaf U₀ Λ)]
    [HasDerivedCategory.{wU₁} (ModuleSheaf U₁ Λ)]
    [HasDerivedCategory.{wX₀} (ModuleSheaf X₀ Λ)]
    [HasDerivedCategory.{wX₁} (ModuleSheaf X₁ Λ)] :
    moduleDerivedDirectImage Λ g ⋙ moduleDerivedLowerShriek j₀ Λ ⟶
      moduleDerivedLowerShriek j₁ Λ ⋙ moduleDerivedDirectImage Λ f :=
  (mateEquiv (moduleDerivedAdjunction Λ g) (moduleDerivedAdjunction Λ f)
    (TwoSquare.mk _ _ _ _
      (moduleDerivedLowerShriekCartesianBaseChangeIso g j₁ j₀ f h Λ).hom)).natTrans

end AlgebraicGeometry.Scheme.EtaleCohomology
