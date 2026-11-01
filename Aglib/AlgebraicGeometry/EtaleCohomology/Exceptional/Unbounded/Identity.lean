/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperNormalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralComparisons

/-! # The original identity normalization of the unbounded exceptional image

The identity is contracted through the literal proper compactification and the
original unbounded direct-image identity. Its middle derived model remains
independent of the endpoint. Binary compositor unit laws are separate assertions.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wM
variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
  [endpointModel : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [middleModels : ∀ C : Hom.DenseCompactification (𝟙 X),
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- The original contraction of the literal identity compactification. -/
def moduleUnboundedIdentityCompactificationIso :
    @moduleUnboundedCompactificationFunctor X X (𝟙 X) Λ _ endpointModel endpointModel
        (Hom.DenseCompactification.ofProper (𝟙 X))
        (middleModels (Hom.DenseCompactification.ofProper (𝟙 X))) ≅
      𝟭 (DerivedCategory (ModuleSheaf X Λ)) :=
  moduleUnboundedProperCompactificationNormalizationIso (𝟙 X) Λ ≪≫
    moduleUnboundedDerivedDirectImageIdIso Λ X

variable [CompactSpace X] [QuasiSeparatedSpace X]
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The chosen epsilon retains the original canonical exceptional-to-ordinary map. -/
def moduleExceptionalDirectImageUnboundedIdIso :
    @moduleExceptionalDirectImageUnbounded X X _ _ (𝟙 X) _ _ _ Λ _
        endpointModel endpointModel (middleModels (moduleExceptionalCompactification (𝟙 X))) ≅
      𝟭 (DerivedCategory (ModuleSheaf X Λ)) :=
  moduleExceptionalDirectImageUnboundedIso (𝟙 X) Λ N hN hΛ
      (Hom.DenseCompactification.ofProper (𝟙 X)) ≪≫
    moduleUnboundedIdentityCompactificationIso X Λ

/-- Epsilon is the same original exceptional comparison followed by the original
unbounded direct-image identity, not a newly chosen equivalence. -/
theorem moduleExceptionalDirectImageUnboundedIdIso_hom :
    (moduleExceptionalDirectImageUnboundedIdIso X Λ N hN hΛ).hom =
      moduleExceptionalToDirectImageUnbounded (𝟙 X) Λ ≫
        (moduleUnboundedDerivedDirectImageIdIso Λ X).hom := by
  simp only [moduleExceptionalDirectImageUnboundedIdIso,
    moduleUnboundedIdentityCompactificationIso, Iso.trans_hom, ← Category.assoc]
  exact congrArg (fun t => t ≫ (moduleUnboundedDerivedDirectImageIdIso Λ X).hom)
    (moduleExceptionalUnboundedProperNormalizationIso_hom (𝟙 X) Λ N hN hΛ)

end AlgebraicGeometry.Scheme.EtaleCohomology
