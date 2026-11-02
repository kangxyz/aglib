/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.Pasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIsoBeforeOpen

/-! # Actual source transport before the original open/proper exchange -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX₀ wX₁ wX₂ wM₀ wM₂ wS wT
variable {X₀ X₁ X₂ M₀ M₂ S T : Scheme.{u}}
  (j₀ : X₀ ⟶ M₀) (p₀ : M₀ ⟶ S) (e : X₁ ≅ X₀)
  (j₂ : X₂ ⟶ M₂) (p₂ : M₂ ⟶ T)
  (a : X₂ ⟶ X₁) (q : M₂ ⟶ M₀) (b : T ⟶ S)
  [IsOpenImmersion j₀] [IsOpenImmersion j₂]
  (hj : IsPullback a j₂ (e.hom ≫ j₀) q)
  (ht : IsPullback (a ≫ e.hom) j₂ j₀ q) (hp : IsPullback q p₂ p₀ b)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX₀} (ModuleSheaf X₀ Λ)]
  [HasDerivedCategory.{wX₁} (ModuleSheaf X₁ Λ)]
  [HasDerivedCategory.{wX₂} (ModuleSheaf X₂ Λ)]
  [HasDerivedCategory.{wM₀} (ModuleSheaf M₀ Λ)]
  [HasDerivedCategory.{wM₂} (ModuleSheaf M₂ Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]

/-- The original source-isomorphism comparison commutes with the following
original compactified exchange by proper-exchange naturality and actual open pasting. -/
theorem moduleUnboundedCompactifiedBaseChangeMap_sourceIso_before :
    SourceIsoBeforeExchangeEquation (moduleUnboundedCompactifiedSourceIso e j₀ p₀ Λ)
      (moduleUnboundedCompactifiedBaseChangeMap (e.hom ≫ j₀) p₀ j₂ p₂ a q b hj hp Λ)
      (moduleUnboundedCompactifiedBaseChangeMap j₀ p₀ j₂ p₂ (a ≫ e.hom) q b ht hp Λ)
      (moduleUnboundedDerivedInverseImageCompIso Λ e.hom a) :=
  sourceIsoBeforeExchange_of_open (moduleUnboundedDerivedLowerShriekSourceIso e j₀ Λ)
    (moduleUnboundedDerivedBaseChangeMap Λ p₀ p₂ b q hp.w.symm)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a j₂ (e.hom ≫ j₀) q hj Λ)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso (a ≫ e.hom) j₂ j₀ q ht Λ)
    (moduleUnboundedDerivedInverseImageCompIso Λ e.hom a)
    (moduleUnboundedDerivedOpenComparison_sourceIso_before j₀ e j₂ a q hj ht Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
