/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.UnitModelFamily
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.FamilyArrowComparison

/-! # Original arrow and family transport preserve the comparison to a single original value -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM₀ wM₁ wC
variable {X S : Scheme.{u}} {f g : X ⟶ S} [QuasiCompact f] [QuasiCompact g]
  [CompactSpace S] [QuasiSeparatedSpace S]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
  (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)) (e : f = g)
  (models₀ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM₀} (ModuleSheaf C.Xbar Λ))
  (C : Hom.DenseCompactification f)
  (hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ))

/-- Equality of the original scheme arrows changes no single-value comparison map. -/
theorem moduleExceptionalSingleTorsionValueIso_arrow :
    moduleExceptionalDirectImagePlusTorsionArrowIso Λ hX hS e models₀ ≪≫
      moduleExceptionalSingleTorsionValueIso (hX := hX) (hS := hS)
        (models := moduleCompactificationModelFamilyCongr Λ e models₀)
        g Λ (Hom.DenseCompactification.ofArrowEq e C) hC =
    moduleExceptionalSingleTorsionValueIso (hX := hX) (hS := hS)
      (models := models₀) f Λ C hC := by
  subst g
  change Iso.refl _ ≪≫ _ = _
  exact Iso.refl_trans _

variable (models₁ : ∀ C : Hom.DenseCompactification g,
    HasDerivedCategory.{wM₁} (ModuleSheaf C.Xbar Λ))

/-- The canonical arrow-plus-family normalization commutes with the same original value. -/
theorem moduleExceptionalSingleTorsionValueIso_congr :
    moduleExceptionalDirectImagePlusTorsionCongr Λ hX hS e models₀ models₁ ≪≫
      moduleExceptionalSingleTorsionValueIso (hX := hX) (hS := hS)
        (models := models₁) g Λ (Hom.DenseCompactification.ofArrowEq e C) hC =
    moduleExceptionalSingleTorsionValueIso (hX := hX) (hS := hS)
      (models := models₀) f Λ C hC := by
  have hf := moduleExceptionalSingleTorsionValueIso_family g Λ hX hS
    (moduleCompactificationModelFamilyCongr Λ e models₀) models₁
    (Hom.DenseCompactification.ofArrowEq e C) hC
  have ht := congrArg
    (fun z => moduleExceptionalDirectImagePlusTorsionArrowIso Λ hX hS e models₀ ≪≫ z) hf
  exact (Iso.trans_assoc
    (moduleExceptionalDirectImagePlusTorsionArrowIso Λ hX hS e models₀)
    (moduleExceptionalDirectImagePlusTorsionFamilyComparison g Λ hX hS
      (moduleCompactificationModelFamilyCongr Λ e models₀) models₁)
    (moduleExceptionalSingleTorsionValueIso (hX := hX) (hS := hS)
      (models := models₁) g Λ (Hom.DenseCompactification.ofArrowEq e C) hC)).trans
    (ht.trans (moduleExceptionalSingleTorsionValueIso_arrow Λ hX hS e models₀ C hC))

end AlgebraicGeometry.Scheme.EtaleCohomology
