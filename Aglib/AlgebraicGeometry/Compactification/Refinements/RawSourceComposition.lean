/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.SourceIsoCoherence

/-! # Actual successive source-transport compactifications -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Hom.DenseCompactification

universe u
variable {X₀ X₁ X₂ S : Scheme.{u}} (f₀ : X₀ ⟶ S) (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
  (e₁ : X₁ ≅ X₀) (e₂ : X₂ ≅ X₁) (h₁ : e₁.hom ≫ f₀ = f₁)
  (h₂ : e₂.hom ≫ f₁ = f₂) (C : Hom.DenseCompactification f₀)

abbrev rawSourceFirstModel := (sourceIso f₁ e₁ h₁).obj C

abbrev rawSourceSequentialModel :=
  (sourceIso f₂ e₂ h₂).obj (rawSourceFirstModel f₀ f₁ e₁ h₁ C)

abbrev rawSourceCompositeModel :=
  (sourceIso f₂ (e₂ ≪≫ e₁) (sourceIso_comp_fac f₀ f₁ f₂ e₁ e₂ h₁ h₂)).obj C

end AlgebraicGeometry.Scheme.EtaleCohomology
