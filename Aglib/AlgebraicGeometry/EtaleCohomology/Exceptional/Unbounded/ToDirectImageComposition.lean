/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.Composition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ToDirectImageCompositionModel

/-! # The chosen compositor preserves the same canonical exceptional-to-ordinary map -/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wY wZ wF wG wFG
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [QuasiCompact f] [QuasiCompact g]
  [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Z] [QuasiSeparatedSpace Z]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [firstModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]
  [secondModels : ∀ C : Hom.DenseCompactification g,
    HasDerivedCategory.{wG} (ModuleSheaf C.Xbar Λ)]
  [compositeModels : ∀ C : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wFG} (ModuleSheaf C.Xbar Λ)]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Computed through any supplied tower, the original chosen compositor commutes with
exactly the same canonical maps and the original ordinary direct-image compositor. -/
theorem moduleExceptionalToDirectImageUnbounded_composition_model
    (C : Hom.CompactifiedComposition f g) :
    CompositionToTargetEquation
      (R := moduleUnboundedDerivedDirectImage Λ f)
      (S := moduleUnboundedDerivedDirectImage Λ g)
      (T := moduleUnboundedDerivedDirectImage Λ (f ≫ g))
      (F := moduleExceptionalDirectImageUnbounded f Λ)
      (G := moduleExceptionalDirectImageUnbounded g Λ)
      (H := moduleExceptionalDirectImageUnbounded (f ≫ g) Λ)
      (𝟭 (DerivedCategory (ModuleSheaf X Λ)))
      (𝟭 (DerivedCategory (ModuleSheaf Y Λ))) (𝟭 (DerivedCategory (ModuleSheaf Z Λ)))
      (moduleExceptionalToDirectImageUnbounded f Λ) (moduleExceptionalToDirectImageUnbounded g Λ)
      (moduleExceptionalToDirectImageUnbounded (f ≫ g) Λ)
      (moduleExceptionalDirectImageUnboundedCompIso f g Λ N hN hΛ)
      (moduleUnboundedDerivedDirectImageCompIso Λ g f).symm :=
  compositionToTarget_transport
    (F := moduleExceptionalDirectImageUnbounded f Λ)
    (G := moduleExceptionalDirectImageUnbounded g Λ)
    (H := moduleExceptionalDirectImageUnbounded (f ≫ g) Λ)
    (Fm := moduleUnboundedCompactificationFunctor f Λ C.first)
    (Gm := moduleUnboundedCompactificationFunctor g Λ C.targetCompactification)
    (Hm := moduleUnboundedCompactificationFunctor (f ≫ g) Λ C.composite)
    (𝟭 (DerivedCategory (ModuleSheaf X Λ)))
    (𝟭 (DerivedCategory (ModuleSheaf Y Λ))) (𝟭 (DerivedCategory (ModuleSheaf Z Λ)))
    (moduleExceptionalToDirectImageUnbounded f Λ) (moduleExceptionalToDirectImageUnbounded g Λ)
    (moduleExceptionalToDirectImageUnbounded (f ≫ g) Λ)
    (moduleUnboundedCompactificationToDirectImage f Λ C.first)
    (moduleUnboundedCompactificationToDirectImage g Λ C.targetCompactification)
    (moduleUnboundedCompactificationToDirectImage (f ≫ g) Λ C.composite)
    (moduleExceptionalDirectImageUnboundedCompIso f g Λ N hN hΛ)
    (moduleUnboundedCompactifiedCompositionIso f g Λ C N hN hΛ)
    (moduleUnboundedDerivedDirectImageCompIso Λ g f).symm
    (moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ C.first)
    (moduleExceptionalDirectImageUnboundedIso g Λ N hN hΛ C.targetCompactification)
    (moduleExceptionalDirectImageUnboundedIso (f ≫ g) Λ N hN hΛ C.composite)
    (moduleExceptionalToDirectImageUnbounded_model f Λ N hN hΛ C.first)
    (moduleExceptionalToDirectImageUnbounded_model g Λ N hN hΛ C.targetCompactification)
    (moduleExceptionalToDirectImageUnbounded_model (f ≫ g) Λ N hN hΛ C.composite)
    (moduleExceptionalDirectImageUnboundedCompIso_comparison f g Λ N hN hΛ C)
    (moduleUnboundedCompactifiedCompositionIso_toDirectImage f g Λ C N hN hΛ)
end AlgebraicGeometry.Scheme.EtaleCohomology
