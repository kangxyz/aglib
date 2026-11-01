/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.IdentityAmbientComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.LowerShriekComposition

/-! # Original identity-ambient comparison retains both actual arrow equalities -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wS
variable {X Y S : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

/-- Equality of open arrows is retained when a transported source
uses an identity composite. -/
theorem moduleRawImageComparison_identity_eq_both
    (j₀ j₁ : X ⟶ Y) [IsOpenImmersion j₀] [IsOpenImmersion j₁]
    (sq : IsPullback j₀ (𝟙 X) (𝟙 Y) j₁) (ej : j₁ = j₀)
    (p₀ p₁ : Y ⟶ S) (ep : p₁ = p₀) :
    CategoryTheory.imageComparison
      (moduleDerivedProperRefinementComparison j₀ j₁ (𝟙 Y) sq Λ)
      (moduleDerivedDirectImageOverIso Λ p₀ p₁ (𝟙 Y) ((Category.id_comp p₁).trans ep)) =
    Functor.whiskerRight (eqToHom (moduleDerivedLowerShriek_congr Λ ej))
        (moduleDerivedDirectImage Λ p₁) ≫
      Functor.whiskerLeft (moduleDerivedLowerShriek j₀ Λ)
        (eqToHom (congrArg (fun p : Y ⟶ S => moduleDerivedDirectImage Λ p) ep)) := by
  subst j₁
  simpa only [eqToHom_refl, Functor.whiskerRight_id', Category.id_comp] using
    (moduleRawImageComparison_identity_eq j₀ sq Λ p₀ p₁ ep)

end AlgebraicGeometry.Scheme.EtaleCohomology
