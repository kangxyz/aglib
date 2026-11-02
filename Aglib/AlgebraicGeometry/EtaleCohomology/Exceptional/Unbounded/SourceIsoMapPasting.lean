/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.Pasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIsoPasting


/-! # Actual compactified base change followed by source-isomorphism transport -/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wU₀ wU₁ wU₂ wM₀ wM₁ wS₀ wS₁

variable {U₀ U₁ U₂ M₀ M₁ S₀ S₁ : Scheme.{u}}
  (j₀ : U₀ ⟶ M₀) (p₀ : M₀ ⟶ S₀) (j₁ : U₁ ⟶ M₁) (p₁ : M₁ ⟶ S₁)
  (a : U₁ ⟶ U₀) (q : M₁ ⟶ M₀) (b : S₁ ⟶ S₀)
  [IsOpenImmersion j₀] [IsOpenImmersion j₁] (e : U₂ ≅ U₁)
  (hj : IsPullback a j₁ j₀ q) (hp : IsPullback q p₁ p₀ b)
  (hj' : IsPullback (e.hom ≫ a) (e.hom ≫ j₁) j₀ q)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wU₀} (ModuleSheaf U₀ Λ)]
  [HasDerivedCategory.{wU₁} (ModuleSheaf U₁ Λ)]
  [HasDerivedCategory.{wU₂} (ModuleSheaf U₂ Λ)]
  [HasDerivedCategory.{wM₀} (ModuleSheaf M₀ Λ)]
  [HasDerivedCategory.{wM₁} (ModuleSheaf M₁ Λ)]
  [HasDerivedCategory.{wS₀} (ModuleSheaf S₀ Λ)]
  [HasDerivedCategory.{wS₁} (ModuleSheaf S₁ Λ)]

/-- The original exchange to the source-transported model is the original
one-step exchange followed by the actual source-isomorphism comparison. -/
theorem moduleUnboundedCompactifiedBaseChangeMap_sourceIso_pasting :
    CompactifiedSourceIsoPastingEquation
      (moduleUnboundedCompactifiedBaseChangeMap j₀ p₀ j₁ p₁ a q b hj hp Λ)
      (moduleUnboundedCompactifiedBaseChangeMap j₀ p₀ (e.hom ≫ j₁) p₁ (e.hom ≫ a) q b hj' hp Λ)
      (moduleUnboundedDerivedInverseImageCompIso Λ a e.hom)
          (moduleUnboundedCompactifiedSourceIso e j₁ p₁ Λ) :=
  compactifiedSourceIsoPasting_of_open
    (moduleUnboundedDerivedBaseChangeMap Λ p₀ p₁ b q hp.w.symm)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso a j₁ j₀ q hj Λ)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso (e.hom ≫ a) (e.hom ≫ j₁) j₀ q hj' Λ)
    (moduleUnboundedDerivedLowerShriekSourceIso e j₁ Λ)
        (moduleUnboundedDerivedInverseImageCompIso Λ a e.hom)
    (moduleUnboundedDerivedOpenComparison_sourceIso_pasting j₀ j₁ a q e hj hj' Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
