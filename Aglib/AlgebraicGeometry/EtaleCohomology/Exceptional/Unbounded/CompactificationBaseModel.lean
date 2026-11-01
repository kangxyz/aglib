/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseIdentityModel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawBaseChange

/-! # Original compactification transport between explicitly specified base models -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wM wS₀ wS₁
variable {X S : Scheme.{u}} {f : X ⟶ S} (C : Hom.Compactification f)
  (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS₀ : HasDerivedCategory.{wS₀} (ModuleSheaf S Λ))
  (hS₁ : HasDerivedCategory.{wS₁} (ModuleSheaf S Λ))
  (hM : HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))

/-- The original proper-image change of target model, with the open factor unchanged. -/
def moduleUnboundedRawCompactificationChangeBaseModel :
    @moduleUnboundedRawCompactificationFunctor X S f C Λ _ hX hS₀ hM ⋙
        (moduleUnboundedBaseModelEquivalence Λ S hS₀ hS₁).functor ≅
      @moduleUnboundedRawCompactificationFunctor X S f C Λ _ hX hS₁ hM :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (@moduleUnboundedDerivedLowerShriek _ _ C.j _ Λ _ hX hM)
      (moduleUnboundedDerivedDirectImageChangeBaseModel Λ hS₀ hS₁ C.p hM)

/-- The identity-base normalizer uses the actual inverse-image localization comparison,
then the original right-derived target-model comparison, independently of base change. -/
def moduleUnboundedRawCompactificationBaseIdentityIso :
    @moduleUnboundedRawCompactificationFunctor X S f C Λ _ hX hS₀ hM ⋙
        @moduleUnboundedDerivedInverseImage Λ _ S S (𝟙 S) hS₀ hS₁ ≅
      @moduleUnboundedRawCompactificationFunctor X S f C Λ _ hX hS₁ hM :=
  Functor.isoWhiskerLeft _ (moduleUnboundedDerivedInverseImageIdentityModelIso Λ S hS₀ hS₁) ≪≫
    moduleUnboundedRawCompactificationChangeBaseModel C Λ hX hS₀ hS₁ hM

end AlgebraicGeometry.Scheme.EtaleCohomology
