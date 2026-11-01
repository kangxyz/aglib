/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.UnitIdentityValue
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.UnitModelToDirectImage

/-! # Independent single-model identity contractions give the original chosen epsilon -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

universe u wX wM wC
variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  (hC : HasDerivedCategory.{wC} (ModuleSheaf X Λ))

/-- No new map is introduced by expressing the single identity contraction as an iso. -/
theorem moduleUnboundedSingleIdentityValueIso_hom :
    (moduleUnboundedSingleIdentityValueIso (hX := hX) (hM := hC) X Λ).hom =
      (@moduleUnboundedSingleValueToDirectImage X X (𝟙 X) Λ _ hX hX
        (Hom.DenseCompactification.ofProper (𝟙 X)) hC) ≫
      (@moduleUnboundedDerivedDirectImageIdIso Λ _ X hX).hom := by
  simp only [moduleUnboundedSingleIdentityValueIso, moduleUnboundedSingleValueToDirectImage,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, asIso_hom]
  exact (Category.assoc _ _ _).symm

variable [CompactSpace X] [QuasiSeparatedSpace X]
  [models : ∀ C : Hom.DenseCompactification (𝟙 X),
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Every independently specified identity middle model yields the same original epsilon. -/
theorem moduleExceptionalDirectImageUnboundedIdIso_singleModel :
    moduleExceptionalUnboundedSingleValueIso (hX := hX) (hS := hX) (models := models)
      (𝟙 X) Λ N hN hΛ
        (Hom.DenseCompactification.ofProper (𝟙 X)) hC ≪≫
      moduleUnboundedSingleIdentityValueIso (hX := hX) (hM := hC) X Λ =
    @moduleExceptionalDirectImageUnboundedIdIso X Λ _ hX models _ _ N hN hΛ := by
  apply Iso.ext
  let χ := moduleExceptionalUnboundedSingleValueIso (hX := hX) (hS := hX) (models := models)
    (𝟙 X) Λ N hN hΛ (Hom.DenseCompactification.ofProper (𝟙 X)) hC
  let ε := moduleUnboundedSingleIdentityValueIso (hX := hX) (hM := hC) X Λ
  change χ.hom ≫ ε.hom = _
  have he := congrArg (fun t => χ.hom ≫ t)
    (moduleUnboundedSingleIdentityValueIso_hom (hX := hX) X Λ hC)
  have hc := moduleExceptionalUnboundedSingleValueIso_toDirectImage
    (hX := hX) (hS := hX) (models := models) (𝟙 X) Λ N hN hΛ
    (Hom.DenseCompactification.ofProper (𝟙 X)) hC
  have ht := congrArg (fun t => t ≫ (@moduleUnboundedDerivedDirectImageIdIso Λ _ X hX).hom) hc
  exact he.trans ((Category.assoc _ _ _).symm.trans (ht.trans
    (@moduleExceptionalDirectImageUnboundedIdIso_hom X Λ _ hX models _ _ N hN hΛ).symm))

end AlgebraicGeometry.Scheme.EtaleCohomology
