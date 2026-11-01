/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawIdentityComparison

/-! # Original identity-ambient comparison for equal proper arrows -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wS
variable {X Y S : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
  (sq : IsPullback j (𝟙 X) (𝟙 Y) j) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

/-- The original unit and proper compositor retain precisely the actual proper-arrow equality. -/
theorem moduleUnboundedRawImageComparison_identity_eq
    (p₀ p₁ : Y ⟶ S) (e : p₁ = p₀) :
    CategoryTheory.imageComparison
      (moduleUnboundedDerivedProperRefinementComparison j j (𝟙 Y) sq Λ)
      (moduleUnboundedDerivedDirectImageOverIso Λ p₀ p₁ (𝟙 Y) ((Category.id_comp p₁).trans e)) =
    Functor.whiskerLeft (moduleUnboundedDerivedLowerShriek j Λ)
      (eqToHom (congrArg (fun p : Y ⟶ S => moduleUnboundedDerivedDirectImage Λ p) e)) := by
  subst p₀
  simpa only [eqToHom_refl, Functor.whiskerLeft_id'] using
    (moduleUnboundedRawImageComparison_id j sq Λ p₁)

end AlgebraicGeometry.Scheme.EtaleCohomology
