/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.ToDirectImageCompatibility
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.ToDirectImageSquare
public import Aglib.CategoryTheory.Adjunction.TripleMateStructural

/-! # Original proper/open exchange commutes with the canonical `j! → Rj*`

The right comparison is the native direct-image composition square, not a
replacement map. Neither properness nor torsion is needed for this equality.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wU₀ wU₁ wX₀ wX₁
variable (Λ : Type (u + 1)) [Ring Λ]
  {U₀ U₁ X₀ X₁ : Scheme.{u}}
  (j₀ : U₀ ⟶ X₀) (j₁ : U₁ ⟶ X₁) (g : U₁ ⟶ U₀) (f : X₁ ⟶ X₀)
  [IsOpenImmersion j₀] [IsOpenImmersion j₁] (h : IsPullback g j₁ j₀ f)
  [HasDerivedCategory.{wU₀} (ModuleSheaf U₀ Λ)]
  [HasDerivedCategory.{wU₁} (ModuleSheaf U₁ Λ)]
  [HasDerivedCategory.{wX₀} (ModuleSheaf X₀ Λ)]
  [HasDerivedCategory.{wX₁} (ModuleSheaf X₁ Λ)]

/-- The actual original mixed mate preserves both canonical outer-adjoint maps. -/
theorem moduleProperOpenMate_toDirectImageSquare :
    Adjunction.TripleMateStructuralEquation
      (moduleDerivedOpenTriple Λ j₀) (moduleDerivedOpenTriple Λ j₁)
      (moduleProperOpenMate Λ j₀ j₁ g f h)
      (moduleDerivedDirectImageSquareIso Λ f g j₀ j₁ h.w).hom := by
  apply Adjunction.tripleMateStructuralEquation _ _
    (moduleDerivedCartesianExchangeIso g j₁ j₀ f h Λ)
    _ _ (moduleProperOpenMate_toDirectImage Λ j₀ j₁ g f h)
  rw [moduleDerivedCartesianExchangeIso_hom]
  exact mate_moduleDerivedBaseChangeMap Λ f g j₀ j₁ h.w

end AlgebraicGeometry.Scheme.EtaleCohomology
