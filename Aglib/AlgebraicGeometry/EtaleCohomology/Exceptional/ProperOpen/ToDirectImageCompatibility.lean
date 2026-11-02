/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.Mate
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenFullyFaithful
public import Aglib.CategoryTheory.Adjunction.TripleMateCompatibility

/-! # The original proper/open mate preserves the canonical outer-adjoint comparison

The comparison is Mathlib's canonical map for the actual native adjoint triple.
The right square is still the mate of the original Cartesian exchange. Its
identification with structural direct-image composition is a separate step.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wU₀ wU₁ wX₀ wX₁
variable (Λ : Type (u + 1)) [Ring Λ]

/-- The original three installed derived functors and both original adjunctions. -/
def moduleDerivedOpenTriple {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [HasDerivedCategory.{wU₀} (ModuleSheaf U Λ)]
    [HasDerivedCategory.{wX₀} (ModuleSheaf X Λ)] :
    Adjunction.Triple (moduleDerivedLowerShriek j Λ)
      (moduleDerivedInverseImage Λ j) (moduleDerivedDirectImage Λ j) where
  adj₁ := moduleDerivedLowerShriekAdjunction j Λ
  adj₂ := moduleDerivedAdjunction Λ j

/-- The canonical outer-adjoint map, not a second independently chosen comparison. -/
abbrev moduleDerivedLowerShriekToDirectImage {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    [HasDerivedCategory.{wU₀} (ModuleSheaf U Λ)]
    [HasDerivedCategory.{wX₀} (ModuleSheaf X Λ)] :=
  (moduleDerivedOpenTriple Λ j).leftToRight

variable {U₀ U₁ X₀ X₁ : Scheme.{u}}
  (j₀ : U₀ ⟶ X₀) (j₁ : U₁ ⟶ X₁) (g : U₁ ⟶ U₀) (f : X₁ ⟶ X₀)
  [IsOpenImmersion j₀] [IsOpenImmersion j₁]
  (h : IsPullback g j₁ j₀ f)
  [HasDerivedCategory.{wU₀} (ModuleSheaf U₀ Λ)]
  [HasDerivedCategory.{wU₁} (ModuleSheaf U₁ Λ)]
  [HasDerivedCategory.{wX₀} (ModuleSheaf X₀ Λ)]
  [HasDerivedCategory.{wX₁} (ModuleSheaf X₁ Λ)]

/-- The unchanged global mixed mate preserves the original canonical `j! → Rj*` maps. -/
theorem moduleProperOpenMate_toDirectImage :
    Adjunction.TripleMateCompatibilityEquation
      (moduleDerivedOpenTriple Λ j₀) (moduleDerivedOpenTriple Λ j₁)
      (moduleDerivedCartesianExchangeIso g j₁ j₀ f h Λ)
      (moduleProperOpenMate Λ j₀ j₁ g f h) :=
  Adjunction.tripleMateCompatibilityEquation _ _ _ _
    (Adjunction.tripleMateTransposeEquation _ _ _
      (moduleDerivedAdjunction Λ f) (moduleDerivedAdjunction Λ g)
      (moduleDerivedLowerShriekCartesianBaseChangeIso g j₁ j₀ f h Λ).hom
      (conjugateEquiv_moduleDerivedLowerShriekCartesianBaseChangeIso_hom g j₁ j₀ f h Λ))

end AlgebraicGeometry.Scheme.EtaleCohomology
