/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIsoComposition

/-! # Original source composition through an actual equality of scheme isomorphisms -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX₀ wX₁ wX₂ wS wM₀ wM₁ wM₂
variable {X₀ X₁ X₂ S : Scheme.{u}} (f₀ : X₀ ⟶ S) (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
  [QuasiCompact f₀] [QuasiCompact f₁] [QuasiCompact f₂]
  (e₁ : X₁ ≅ X₀) (e₂ : X₂ ≅ X₁) (h₁ : e₁.hom ≫ f₀ = f₁)
  (h₂ : e₂.hom ≫ f₁ = f₂) (Λ : Type (u + 1)) [Ring Λ]
  [hX₀ : HasDerivedCategory.{wX₀} (ModuleSheaf X₀ Λ)]
  [hX₁ : HasDerivedCategory.{wX₁} (ModuleSheaf X₁ Λ)]
  [hX₂ : HasDerivedCategory.{wX₂} (ModuleSheaf X₂ Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [sourceModels : ∀ D : Hom.DenseCompactification f₀,
    HasDerivedCategory.{wM₀} (ModuleSheaf D.Xbar Λ)]
  [middleModels : ∀ D : Hom.DenseCompactification f₁,
    HasDerivedCategory.{wM₁} (ModuleSheaf D.Xbar Λ)]
  [targetModels : ∀ D : Hom.DenseCompactification f₂,
    HasDerivedCategory.{wM₂} (ModuleSheaf D.Xbar Λ)]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

variable [Nonempty (Hom.DenseCompactification f₀)]
  [Nonempty (Hom.DenseCompactification f₁)] [Nonempty (Hom.DenseCompactification f₂)]

/-- A proved equality with the actual composite source isomorphism gives the same
original source-composition equation, with its literal inverse-image transport. -/
theorem moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty_composition_of_eq
    (e : X₂ ≅ X₀) (he : e.hom ≫ f₀ = f₂) (heq : e = e₂ ≪≫ e₁) :
    SourceIsoCompositionEquation
      (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty f₀ f₁ e₁ h₁ Λ N hN hΛ)
      (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty f₁ f₂ e₂ h₂ Λ N hN hΛ)
      (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty f₀ f₂ e he Λ N hN hΛ)
      (𝟙 _)
      (eqToIso (congrArg (fun z : X₂ ⟶ X₀ => moduleUnboundedDerivedInverseImage Λ z)
          (congrArg Iso.hom heq)) ≪≫
        moduleUnboundedDerivedInverseImageCompIso Λ e₁.hom e₂.hom) := by
  subst e
  simpa only [eqToIso_refl, Iso.refl_trans] using
    moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty_composition
      f₀ f₁ f₂ e₁ e₂ h₁ h₂ Λ N hN hΛ

end AlgebraicGeometry.Scheme.EtaleCohomology
